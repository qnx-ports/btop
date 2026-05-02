/* Copyright 2021 Aristocratos (jakob@qvantnet.com)

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

indent = tab
tab-size = 4
*/

// ---- QNX-specific headers ----
#include <sys/syspage.h>
#include <sys/neutrino.h>
#include <sys/procfs.h>
#include <sys/states.h>
#include <sys/mman.h>
#include <sys/utsname.h>
#include <devctl.h>

// ---- Standard POSIX headers ----
#include <arpa/inet.h>
#include <fcntl.h>
#include <net/if.h>
#include <net/if_dl.h>
#include <net/route.h> 
#include <ifaddrs.h>
#include <netdb.h>
#include <netinet/in.h>
#include <pwd.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/statvfs.h>
#include <sys/sysctl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

// ---- C++ Standard Library ----
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <ctime>
#include <fstream>
#include <sstream>
#include <memory>
#include <numeric>
#include <ranges>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "../btop_config.hpp"
#include "../btop_shared.hpp"
#include "../btop_tools.hpp"

using std::clamp, std::string_literals::operator""s, std::cmp_less, std::cmp_greater;
using std::ifstream, std::numeric_limits, std::streamsize, std::round, std::max, std::min;
namespace fs = std::filesystem;
namespace rng = std::ranges;
using namespace Tools;

namespace Cpu {
    vector<long long> core_old_totals;
    vector<long long> core_old_idles;
    vector<string> available_fields = {"total"};
    vector<string> available_sensors = {"Auto"};
    cpu_info current_cpu;

    std::unordered_map<int, int> core_mapping;

    auto collect(bool no_update) -> cpu_info&;
    string get_cpuName();
    auto get_core_mapping() -> std::unordered_map<int, int>;
} // namespace Cpu

namespace Mem {
	double old_uptime;
} 

namespace Proc {
	constexpr size_t KTHREADD = 1;
	static std::unordered_set<size_t> kernels_procs = {KTHREADD};
}

namespace Shared {
	fs::path procPath;
	long coreCount, page_size, clkTck;

	void init() {
		//? Shared global variables init
		procPath = (fs::is_directory(fs::path("/proc")) and access("/proc", R_OK) != -1) ? "/proc" : "";
		if (procPath.empty())
			throw std::runtime_error( "Proc filesystem not found or no permission to read from it!");

		// CPU count No difference between physical and core count on QNX
		coreCount = (long)_syspage_ptr->num_cpu;
		if (coreCount < 1) {
			coreCount = 1;
			Logger::warning( "Could not determine number of cores, defaulting to 1."); 
		}

		// Page size
		page_size = sysconf(_SC_PAGE_SIZE);
		if (page_size <= 0) {
			page_size = 4096;
			Logger::warning("Could not get system page size. Defaulting to 4096, processes memory usage might be incorrect.");
		}

		// Clock ticks
		clkTck = sysconf(_SC_CLK_TCK);
		if (clkTck <= 0) {
			clkTck = 100;
			Logger::warning( "Could not get system clock ticks per second. Defaulting to 100, processes cpu usage might be incorrect.");
		}

		// Init per-core percent storage
		Cpu::current_cpu.core_percent.insert(Cpu::current_cpu.core_percent.begin(), Shared::coreCount, {});
		Cpu::current_cpu.temp.insert(Cpu::current_cpu.temp.begin(), Shared::coreCount + 1, {});
		Cpu::core_old_totals.insert(Cpu::core_old_totals.begin(), Shared::coreCount, 0);
		Cpu::core_old_idles.insert(Cpu::core_old_idles.begin(), Shared::coreCount, 0);
		for (auto &[field, vec] : Cpu::current_cpu.cpu_percent) {
			if (not vec.empty() and not v_contains(Cpu::available_fields, field))
				Cpu::available_fields.push_back(field);
		}

		Cpu::collect();
		Cpu::cpuName = Cpu::get_cpuName();
		Cpu::core_mapping = Cpu::get_core_mapping();

		Mem::old_uptime = system_uptime();
		Mem::collect();

		Logger::debug("Shared::init() : Initialized.");
	}
} // namespace Shared

namespace Cpu {
	uint64_t last_collect_time_ns = 0;
    string cpuName;
    string cpuHz;
    tuple<int, float, long, string> current_bat = {0, 0.0f, 0L, "not_found"};
	bool got_sensors = false, cpu_temp_only = false, supports_watts = false, has_battery = false;
    /*
       Sadly we do not have the getloadavg() function We also can't really
       calculate this easily in btop since being an RTOS, our threads are almost
       always signal blocked If we wanted to get a proper BSD-style load
       average, we would need see every time a thread enters either READY or
       RUNNING. Since we are bound by the refresh rate of btop, we will miss
       most occurences of this, making any number we come up with complete
       bogus.
       */
    bool has_loadavg = false;

    string get_cpuName() {
		struct cpuinfo_entry *cpuinfo = _SYSPAGE_ENTRY(_syspage_ptr, cpuinfo);
		return SYSPAGE_ENTRY(strings)->data + cpuinfo->name;
    }

    string get_cpuHz() { 
		struct cpuinfo_entry *cpuinfo = _SYSPAGE_ENTRY(_syspage_ptr, cpuinfo);
		uint32_t speed_mhz = cpuinfo->speed; 

		return std::to_string(speed_mhz / 1000.0).substr(0,5) + "GHz";
	}

	auto get_core_mapping() -> std::unordered_map<int, int> {
		std::unordered_map<int, int> core_map;
		if (cpu_temp_only) return core_map;

		for (long i = 0; i < Shared::coreCount; i++) {
			core_map[i] = i;
		}

		//? Apply user set custom mapping if any
		const auto &custom_map = Config::getS("cpu_core_map");
		if (not custom_map.empty()) {
			try {
				for (const auto &split : ssplit(custom_map)) {
					const auto vals = ssplit(split, ':');
					if (vals.size() != 2) continue;
					int change_id = std::stoi(vals.at(0));
					int new_id = std::stoi(vals.at(1));
					if (not core_map.contains(change_id)) continue;
					core_map.at(change_id) = new_id;
				}
			} catch (...) {
			}
		}

		return core_map;
	}

    auto get_battery() -> tuple<int, float, long, string> {
		return current_bat;
    }

    auto collect(bool no_update) -> cpu_info& {
        if (Runner::stopping) return current_cpu;
        if (no_update and not current_cpu.cpu_percent.at("total").empty())
            return current_cpu;

        auto& cpu = current_cpu;

        if (cmp_less(cpu.core_percent.size(), (size_t)Shared::coreCount))
            cpu.core_percent.resize((size_t)Shared::coreCount);

		struct timeval currentTime;
		gettimeofday(&currentTime, nullptr);
		const uint64_t time_now_ns = (currentTime.tv_sec * 1e6 + currentTime.tv_usec) * 1e3;
		uint64_t collect_interval;
		if (last_collect_time_ns == 0) {
			collect_interval = Tools::system_uptime() * 1e9;
		}else {
			collect_interval = time_now_ns - last_collect_time_ns;
		}

		long long global_total_percent = 0;
		struct timespec core_kernel_time;

        // If we measure the kernel busy time, it should give us the cpu idle
        // time (or very close to it) which we can render
		// For more in depth information, this should be rewritten to sum
		// up the cputimes of all processes that are not the kernel

        for (int i = 0; i < Shared::coreCount; i++) {
			try {
				clockid_t cid = ClockId(Proc::KTHREADD, i + 1);
				if (cid == -1) continue;
				clock_gettime(cid, &core_kernel_time);
				uint64_t idle_ns = core_kernel_time.tv_sec * 1e9 + core_kernel_time.tv_nsec;

				uint64_t new_idle_time = idle_ns - core_old_idles.at(i);
				core_old_idles.at(i) = idle_ns;

				double core_usage_percent = clamp((1.0 - (double)new_idle_time / collect_interval) * 100.0, 0.0, 100.0);
				global_total_percent += core_usage_percent;

				cpu.core_percent.at(i).push_back((long long) round(core_usage_percent));

				//? Reduce size if there are more values than needed for graph
				if (cpu.core_percent.at(i).size() > 40) cpu.core_percent.at(i).pop_front();
			} catch (const std::exception &e) {
				Logger::error("Cpu::collect() : " + (string)e.what());
				throw std::runtime_error("collect() : " + (string)e.what());
			}
        }

        last_collect_time_ns = time_now_ns;

		cpu.cpu_percent.at("total").push_back(clamp((long long)round(global_total_percent / Shared::coreCount), 0ll, 100ll));

		if (Config::getB("show_cpu_freq")) {
			auto hz = get_cpuHz();
			if (hz != "") {
				cpuHz = hz;
			}
		}

        return cpu;
    }
} // namespace Cpu

namespace Mem {
	bool has_swap{};
	mem_info current_mem {};
	uint64_t totalRam = 0;
	int disk_ios{};
	vector<string> last_found;

    uint64_t get_totalMem() {
		if (totalRam == 0) Mem::collect();

		return totalRam;
	}

	auto collect(bool no_update) -> mem_info & {
		if (Runner::stopping or (no_update and not current_mem.percent.at("used").empty()))
			return current_mem;

		auto show_disks = Config::getB("show_disks");
		auto &mem = current_mem;

		// read from /proc/vm/stats
		ifstream meminfo(Shared::procPath / "vm/stats");
		if (meminfo.good()) {
			uint64_t cacheRam = 0;
			while (not meminfo.eof()) {
				string label, value_s;
				getline(meminfo, label, '=');
				getline(meminfo, value_s, ' ');
				// some entries are name=val (size), and some are name=val
				if (value_s.length() == 0) getline(meminfo, value_s, '\n');
				else meminfo.ignore(SSmax, '\n');
				// if it's still 0, we can't parse the line, just skip
				if (value_s.length() == 0) continue;

				uint64_t value;
				try {
					 value = std::stoul(value_s, nullptr, 16) * Shared::page_size;
				} catch(...) {
					continue;
				}

				if (label == "page_count") {
					totalRam = value;
				} else if (label == "pages_allocated") {
					mem.stats.at("used") = value;
				} else if (label == "pages_free") {
					mem.stats.at("free") = value;
				} else if (label == "cache_object") {
					cacheRam += value;
				} else if (label == "cache_shmem") {
					cacheRam += value;
				}
			}
			
			mem.stats.at("cached") = cacheRam;
			mem.stats.at("available") = mem.stats.at("free") + cacheRam;
		}else {
			throw std::runtime_error("Failed to read /proc/vm/stats");
		}
		meminfo.close();

		// /proc/vm/stats doesn't show swap information
		mem.stats.at("swap_total") = 0;
		mem.stats.at("swap_used") = 0;
		mem.stats.at("swap_free") = 0;
		has_swap = false;

		if (totalRam > 0) {
			for (const auto& name : mem_names) {
				mem.percent.at(name).push_back(round((double)mem.stats.at(name) * 100 / totalRam));
				while (cmp_greater(mem.percent.at(name).size(), width * 2)) mem.percent.at(name).pop_front();
			}
		}

		if (show_disks) {
			auto &disks = mem.disks;
			const auto &disks_filter = Config::getS("disks_filter");
			vector<string> filter;
			bool filter_exclude = false;
			if (not disks_filter.empty()) {
				filter = ssplit(disks_filter);
				if (filter.at(0).starts_with("exclude=")) {
					filter_exclude = true;
					filter.at(0) = filter.at(0).substr(8);
				}
			}

			vector<string> found;
			{
				// QNX has no /proc/mounts; parse the output of the `mount` command
				// instead. Output format: "<device> on <mountpoint> type <fstype>
				// [options]"
				FILE *mf = popen("mount", "r");
				if (mf != nullptr) {
					char line[1024];
					while (fgets(line, sizeof(line), mf) != nullptr) {
						// Tokenise: dev=token[0], "on"=token[1], mp=token[2],
						// "type"=token[3], fstype=token[4]
						std::istringstream iss(line);
						std::string dev, on, mp, type_kw, fstype;
						if (not(iss >> dev >> on >> mp >> type_kw >> fstype)) continue;
						if (on != "on" or type_kw != "type") continue;

						// Skip virtual / non-storage filesystems
						if (is_in(fstype, "shmem"s, "proc"s, "tmpfs"s, "devfs"s, "autofs"s, "procfs"s, "ifs"s)) continue;

						if (not filter.empty()) {
						bool match = v_contains(filter, mp);
						if ((filter_exclude and match) or (not filter_exclude and not match))
							continue;
						}

						found.push_back(mp);
						if (not disks.contains(mp)) {
							std::error_code ec;
							fs::path dev_path = fs::canonical(dev, ec);
							string disk_name = (mp == "/") ? "root"s : fs::path(mp).filename().string();
							disks[mp] = disk_info{dev_path, disk_name};
							if (disks.at(mp).dev.empty()) disks.at(mp).dev = dev;
							disks.at(mp).fstype = fstype;
						}

						struct statvfs vfs{};
						if (statvfs(mp.c_str(), &vfs) == 0 and vfs.f_blocks > 0) {
							auto &disk = disks.at(mp);
							disk.total = (int64_t)vfs.f_blocks * (int64_t)vfs.f_frsize;
							disk.free = (int64_t)vfs.f_bfree * (int64_t)vfs.f_frsize;
							disk.used = disk.total - disk.free;
							disk.used_percent = (int)round((double)disk.used * 100.0 / disk.total);
							disk.free_percent = 100 - disk.used_percent;
						}
					}
					pclose(mf);
				}
			}

			for (auto it = disks.begin(); it != disks.end();) {
				if (not v_contains(found, it->first))
				it = disks.erase(it);
				else
				++it;
			}
			if (found.size() != last_found.size())
				redraw = true;
			last_found = std::move(found);

			mem.disks_order.clear();
			if (disks.contains("/"))
				mem.disks_order.push_back("/");
			for (const auto &mp : last_found)
				if (mp != "/")
				mem.disks_order.push_back(mp);

			disk_ios = 0;
		}

		return mem;
	}

} // namespace Mem


namespace Net {
    std::unordered_map<string, net_info> current_net;
    net_info empty_net = {};
    vector<string> interfaces;
    string selected_iface;
    int errors = 0;
    bool rescale = true;
    std::unordered_map<string, uint64_t> graph_max = {{"download", 0}, {"upload", 0}};
    std::unordered_map<string, array<int, 2>> max_count = {{"download", {0,0}}, {"upload", {0,0}}};
    uint64_t timestamp = 0;

	// literally a copy paste of the freebsd one since io-sock is based off the freebsd network stack
	auto collect(bool no_update) -> net_info & {
		auto &net = current_net;
		auto &config_iface = Config::getS("net_iface");
		auto net_sync = Config::getB("net_sync");
		auto net_auto = Config::getB("net_auto");
		auto new_timestamp = time_ms();

		if (not no_update and errors < 3) {
			//? Get interface list using getifaddrs() wrapper
			IfAddrsPtr if_addrs {};
			if (if_addrs.get_status() != 0) {
				errors++;
				Logger::error("Net::collect() -> getifaddrs() failed with id " + to_string(if_addrs.get_status()));
				redraw = true;
				return empty_net;
			}
			int family = 0;
			static_assert(INET6_ADDRSTRLEN >= INET_ADDRSTRLEN); // 46 >= 16, compile-time assurance.
			enum { IPBUFFER_MAXSIZE = INET6_ADDRSTRLEN }; // manually using the known biggest value, guarded by the above static_assert
			char ip[IPBUFFER_MAXSIZE];
			interfaces.clear();
			string ipv4, ipv6;

			//? Iteration over all items in getifaddrs() list
			for (auto *ifa = if_addrs.get(); ifa != nullptr; ifa = ifa->ifa_next) {
				if (ifa->ifa_addr == nullptr) continue;
				family = ifa->ifa_addr->sa_family;
				const auto &iface = ifa->ifa_name;
				//? Update available interfaces vector and get status of interface
				if (not v_contains(interfaces, iface)) {
					interfaces.push_back(iface);
					net[iface].connected = (ifa->ifa_flags & IFF_RUNNING);

					// An interface can have more than one IP of the same family associated with it,
					// but we pick only the first one to show in the NET box.
					// Note: Interfaces without any IPv4 and IPv6 set are still valid and monitorable!
					net[iface].ipv4.clear();
					net[iface].ipv6.clear();
				}
				//? Get IPv4 address
				if (family == AF_INET) {
					if (net[iface].ipv4.empty()) {
						if (nullptr != inet_ntop(family, &(reinterpret_cast<struct sockaddr_in*>(ifa->ifa_addr)->sin_addr), ip, IPBUFFER_MAXSIZE)) {

							net[iface].ipv4 = ip;
						} else {
							int errsv = errno;
							Logger::error("Net::collect() -> Failed to convert IPv4 to string for iface " + string(iface) + ", errno: " + strerror(errsv));
						}
					}
				}
				//? Get IPv6 address
				else if (family == AF_INET6) {
					if (net[iface].ipv6.empty()) {
						if (nullptr != inet_ntop(family, &(reinterpret_cast<struct sockaddr_in6*>(ifa->ifa_addr)->sin6_addr), ip, IPBUFFER_MAXSIZE)) {
							net[iface].ipv6 = ip;
						} else {
							int errsv = errno;
							Logger::error("Net::collect() -> Failed to convert IPv6 to string for iface " + string(iface) + ", errno: " + strerror(errsv));
						}
					}
				}  //else, ignoring family==AF_LINK (see man 3 getifaddrs)
			}

			std::unordered_map<string, std::tuple<uint64_t, uint64_t>> ifstats;
			int mib[] = {CTL_NET, PF_ROUTE, 0, 0, NET_RT_IFLIST, 0};
			size_t len;
			if (sysctl(mib, 6, nullptr, &len, nullptr, 0) < 0) {
				Logger::error("failed getting network interfaces");
			} else {
				std::unique_ptr<char[]> buf(new char[len]);
				if (sysctl(mib, 6, buf.get(), &len, nullptr, 0) < 0) {
					Logger::error("failed getting network interfaces");
				} else {
					char *lim = buf.get() + len;
					char *next = nullptr;
					for (next = buf.get(); next < lim;) {
						struct if_msghdr *ifm = (struct if_msghdr *)next;
						next += ifm->ifm_msglen;
						struct if_data ifm_data = ifm->ifm_data;
						if (ifm->ifm_addrs & RTA_IFP) {
							struct sockaddr_dl *sdl = (struct sockaddr_dl *)(ifm + 1);
							char iface[32];
							strncpy(iface, sdl->sdl_data, sdl->sdl_nlen);
							iface[sdl->sdl_nlen] = 0;
							ifstats[iface] = std::tuple(ifm_data.ifi_ibytes, ifm_data.ifi_obytes);
						}
					}
				}
			}

			//? Get total received and transmitted bytes + device address if no ip was found
			for (const auto &iface : interfaces) {
				for (const string dir : {"download", "upload"}) {
					auto &saved_stat = net.at(iface).stat.at(dir);
					auto &bandwidth = net.at(iface).bandwidth.at(dir);
					uint64_t val = dir == "download" ? std::get<0>(ifstats[iface]) : std::get<1>(ifstats[iface]);

					//? Update speed, total and top values
					if (val < saved_stat.last) {
						saved_stat.rollover += saved_stat.last;
						saved_stat.last = 0;
					}
					if (cmp_greater((unsigned long long)saved_stat.rollover + (unsigned long long)val, numeric_limits<uint64_t>::max())) {
						saved_stat.rollover = 0;
						saved_stat.last = 0;
					}
					saved_stat.speed = round((double)(val - saved_stat.last) / ((double)(new_timestamp - timestamp) / 1000));
					if (saved_stat.speed > saved_stat.top) saved_stat.top = saved_stat.speed;
					if (saved_stat.offset > val + saved_stat.rollover) saved_stat.offset = 0;
					saved_stat.total = (val + saved_stat.rollover) - saved_stat.offset;
					saved_stat.last = val;

					//? Add values to graph
					bandwidth.push_back(saved_stat.speed);
					while (cmp_greater(bandwidth.size(), width * 2)) bandwidth.pop_front();

					//? Set counters for auto scaling
					if (net_auto and selected_iface == iface) {
						if (saved_stat.speed > graph_max[dir]) {
							++max_count[dir][0];
							if (max_count[dir][1] > 0) --max_count[dir][1];
						} else if (graph_max[dir] > 10 << 10 and saved_stat.speed < graph_max[dir] / 10) {
							++max_count[dir][1];
							if (max_count[dir][0] > 0) --max_count[dir][0];
						}
					}
				}
			}

			//? Clean up net map if needed
			if (net.size() > interfaces.size()) {
				for (auto it = net.begin(); it != net.end();) {
					if (not v_contains(interfaces, it->first))
						it = net.erase(it);
					else
						it++;
				}
			}

			timestamp = new_timestamp;
		}
		//? Return empty net_info struct if no interfaces was found
		if (net.empty())
			return empty_net;

		//? Find an interface to display if selected isn't set or valid
		if (selected_iface.empty() or not v_contains(interfaces, selected_iface)) {
			max_count["download"][0] = max_count["download"][1] = max_count["upload"][0] = max_count["upload"][1] = 0;
			redraw = true;
			if (net_auto) rescale = true;
			if (not config_iface.empty() and v_contains(interfaces, config_iface))
				selected_iface = config_iface;
			else {
				//? Sort interfaces by total upload + download bytes
				auto sorted_interfaces = interfaces;
				rng::sort(sorted_interfaces, [&](const auto &a, const auto &b) {
					return cmp_greater(net.at(a).stat["download"].total + net.at(a).stat["upload"].total,
									   net.at(b).stat["download"].total + net.at(b).stat["upload"].total);
				});
				selected_iface.clear();
				//? Try to set to a connected interface
				for (const auto &iface : sorted_interfaces) {
					if (net.at(iface).connected) selected_iface = iface;
					break;
				}
				//? If no interface is connected set to first available
				if (selected_iface.empty() and not sorted_interfaces.empty())
					selected_iface = sorted_interfaces.at(0);
				else if (sorted_interfaces.empty())
					return empty_net;
			}
		}

		//? Calculate max scale for graphs if needed
		if (net_auto) {
			bool sync = false;
			for (const auto &dir : {"download", "upload"}) {
				for (const auto &sel : {0, 1}) {
					if (rescale or max_count[dir][sel] >= 5) {
						const long long avg_speed = (net[selected_iface].bandwidth[dir].size() > 5
														? std::accumulate(net.at(selected_iface).bandwidth.at(dir).rbegin(), net.at(selected_iface).bandwidth.at(dir).rbegin() + 5, 0ll) / 5
														: net[selected_iface].stat[dir].speed);
						graph_max[dir] = max(uint64_t(avg_speed * (sel == 0 ? 1.3 : 3.0)), (uint64_t)10 << 10);
						max_count[dir][0] = max_count[dir][1] = 0;
						redraw = true;
						if (net_sync) sync = true;
						break;
					}
				}
				//? Sync download/upload graphs if enabled
				if (sync) {
					const auto other = (string(dir) == "upload" ? "download" : "upload");
					graph_max[other] = graph_max[dir];
					max_count[other][0] = max_count[other][1] = 0;
					break;
				}
			}
		}

		rescale = false;
		return net.at(selected_iface);
	}
} // namespace Net

namespace Proc {
    vector<proc_info> current_procs;
    std::unordered_map<string, string> uid_user;
    string current_sort;
    string current_filter;
    bool current_rev = false;
    bool is_tree_mode = false;

    int collapse = -1, expand = -1, toggle_children = -1;
    atomic<int> numpids = 0;
    int filter_found = 0;

    detail_container detailed;
    static std::unordered_set<size_t> dead_procs;

	uint64_t last_collect_time_ns = 0;

	// best attempt at mapping each state to a unique char...
	const std::unordered_map<uint, char> qnx_proc_states = {
		{ STATE_DEAD,			'D' },
		{ STATE_RUNNING,		'r' },
		{ STATE_READY,			'R' },
		{ STATE_STOPPED,		'S' },
		{ STATE_SEND,			'>' },  // arrow out, like sending
		{ STATE_RECEIVE,		'<' },  // arrow in, like receiving
		{ STATE_REPLY,			'=' },  // equal, a reply for a response
		{ STATE_MQ_SEND,		')' },  // like Send and Receive, but () 
		{ STATE_MQ_RECEIVE,		'(' },  // because q is round
		{ STATE_WAITPAGE,		'W' },  
		{ STATE_SIGSUSPEND,		'x' },  // suspend is mild destroy
		{ STATE_SIGWAITINFO,	'.' },  // . is like a loading ellipsis
		{ STATE_NANOSLEEP,		'n' },  
		{ STATE_MUTEX,			'M' },  
		{ STATE_CONDVAR,		'C' },  
		{ STATE_JOIN,			'J' },  
		{ STATE_INTR,			'i' },  
		{ STATE_SEM,			's' },  
		{ STATE_WAITCTX,		'w' },  
		{ STATE_RWLOCK_READ,	'[' },  // Like MqSend and MqReceive but lock
		{ STATE_RWLOCK_WRITE,	']' },  // sounds like block, so square braces
		{ STATE_BARRIER,		'B' },  
		{ STATE_PIPE,			'|' },  // pipe symbol
		{ STATE_TIMEOUT_MAX,	'T' },  
		{ STATE_CREATE,			'c' },  
		{ STATE_DESTROY,		'X' },  // Cross it out to destroy
		{ STATE_MUON_MUTEX,		'u' },  
		{ STATE_TRACEBUFFER,	'-' },  // trace, like a line
		{ STATE_INTR_ATTACH_EV,	'I' },  
		{ STATE_TIMER_DELEGATE,	'd' },  // d for delegate
		// State Unknown is not here, but it is represented with U
	};

	const std::unordered_map<char, string> qnx_detailed_proc_states = {
		{ 'D', "Dead" },
		{ 'r', "Running" },
		{ 'R', "Ready" },
		{ 'S', "Stopped" },
		{ '>', "Send" },
		{ '<', "Receive" },
		{ '=', "Reply" },
		{ ')', "MqSend" },
		{ '(', "MqReceive" },
		{ 'W', "Waitpage" },
		{ 'x', "Sigsuspend" },
		{ '.', "Sigwaitinfo" },
		{ 'n', "Nanosleep" },
		{ 'M', "Mutex" },
		{ 'C', "Condvar" },
		{ 'J', "Join" },
		{ 'i', "Intr" },
		{ 's', "Sem" },
		{ 'w', "Waitctx" },
		{ '[', "RwlockRead" },
		{ ']', "RwlockWrite" },
		{ 'B', "Barrier" },
		{ '|', "Pipe" },
		{ 'T', "TimeoutMax" },
		{ 'c', "Create" },
		{ 'X', "Destroy" },
		{ 'u', "MuonMutex" },
		{ '-', "Tracebuffer" },
		{ 'I', "IntrAttachEv" },
		{ 'd', "TimerDelegate" },
		{ 'U', "Unknown"},
	};

	//* Get detailed info for selected process
	void _collect_details(const size_t pid, vector<proc_info> &procs) {
		if (pid != detailed.last_pid) {
			detailed = {};
			detailed.last_pid = pid;
			detailed.skip_smaps = not Config::getB("proc_info_smaps");
		}

		//? Copy proc_info for process from proc vector
		auto p_info = rng::find(procs, pid, &proc_info::pid);
		detailed.entry = *p_info;

		//? Update cpu percent deque for process cpu graph
		if (not Config::getB("proc_per_core")) detailed.entry.cpu_p *= Shared::coreCount;
		detailed.cpu_percent.push_back(clamp((long long)round(detailed.entry.cpu_p), 0ll, 100ll));
		while (cmp_greater(detailed.cpu_percent.size(), width)) detailed.cpu_percent.pop_front();

		//? Process runtime : current time - start time (both in unix time - seconds since epoch)
		struct timeval currentTime;
		gettimeofday(&currentTime, nullptr);
		// only interested in second granularity, so ignoring tc_usec
		if (detailed.entry.state != 'X') detailed.elapsed = sec_to_dhms(currentTime.tv_sec - detailed.entry.cpu_s); 
		else detailed.elapsed = sec_to_dhms(detailed.entry.death_time);
		if (detailed.elapsed.size() > 8) detailed.elapsed.resize(detailed.elapsed.size() - 3);

		//? Get parent process name
		if (detailed.parent.empty()) {
			auto p_entry = rng::find(procs, detailed.entry.ppid, &proc_info::pid);
			if (p_entry != procs.end()) detailed.parent = p_entry->name;
		}

		//? Expand process status from single char to explanative string
		detailed.status = qnx_detailed_proc_states.at(detailed.entry.state);

		detailed.mem_bytes.push_back(detailed.entry.mem);
		detailed.memory = floating_humanizer(detailed.entry.mem);

		if (detailed.first_mem == -1 or detailed.first_mem < detailed.mem_bytes.back() / 2 or detailed.first_mem > detailed.mem_bytes.back() * 4) {
			detailed.first_mem = min((uint64_t)detailed.mem_bytes.back() * 2, Mem::get_totalMem());
			redraw = true;
		}

		while (cmp_greater(detailed.mem_bytes.size(), width)) detailed.mem_bytes.pop_front();
	}

    auto collect(bool no_update) -> vector<proc_info> & {
		const auto &sorting = Config::getS("proc_sorting");
		auto reverse = Config::getB("proc_reversed");
		const auto &filter = Config::getS("proc_filter");
		auto per_core = Config::getB("proc_per_core");
		auto should_filter_kernel = Config::getB("proc_filter_kernel");
		auto tree = Config::getB("proc_tree");
		auto show_detailed = Config::getB("show_detailed");
		const auto pause_proc_list = Config::getB("pause_proc_list");
		const size_t detailed_pid = Config::getI("detailed_pid");

        bool should_filter = (current_filter != filter);
        if (should_filter) current_filter = filter;
        bool sorted_change = (sorting != current_sort or reverse != current_rev or should_filter);
        bool tree_mode_change = (tree != is_tree_mode);
        if (sorted_change) {
			current_sort = sorting;
			current_rev = reverse; 
		}
        if (tree_mode_change) is_tree_mode = tree;

        const int cmult = per_core ? (int)Shared::coreCount : 1;
        bool got_detailed = false;

		static size_t proc_clear_count{};

        static vector<size_t> found;

        if (no_update and not current_procs.empty()) {
            if (show_detailed and detailed_pid != detailed.last_pid)
                _collect_details(detailed_pid, current_procs);
        } else {
            should_filter = true;
            found.clear();
			struct timeval currentTime;
			gettimeofday(&currentTime, nullptr);
			const uint64_t time_now_ns = (currentTime.tv_sec * 1e6 + currentTime.tv_usec) * 1e3;

			//? First make sure kernel proc cache is cleared.
			if (should_filter_kernel and ++proc_clear_count >= 256) {
				//? Clearing the cache is used in the event of a pid wrap around.
				//? In that event processes that acquire old kernel pids would also be filtered out so we need to manually clean the cache every now and then.
				kernels_procs.clear();
				kernels_procs.emplace(KTHREADD);
				proc_clear_count = 0;
			}

            std::error_code dir_errorcode;
            for (const fs::path &dir_entry : fs::directory_iterator(Shared::procPath, dir_errorcode)) {
                if (dir_errorcode) continue;
                const auto &proc_pid = dir_entry.filename().string();
                if (proc_pid.empty() or not std::isdigit((unsigned char)proc_pid[0])) continue;

                size_t pid = 0;
                try {
					pid = std::stoul(proc_pid); 
				} catch (...) {
					continue; 
				}
                if (pid < 1) continue;

				if (should_filter_kernel and kernels_procs.contains(pid)) {
					continue;
				}

                found.push_back(pid);

                bool no_cache = false;
                auto find_old = rng::find(current_procs, pid, &proc_info::pid);
                if (find_old == current_procs.end()) {
                    if (not pause_proc_list) {
                        current_procs.push_back({pid});
                        find_old = current_procs.end() - 1;
                        no_cache = true;
                    } else continue;
                } else if (dead_procs.contains(pid)) continue;

                auto& new_proc = *find_old;

				fs::path ctl_path = dir_entry / "ctl";
                int ctl_fd = open(ctl_path.c_str(), O_RDONLY);

                procfs_info info{};
                if (devctl(ctl_fd, DCMD_PROC_INFO, &info, sizeof(info), nullptr) != EOK) {
                    close(ctl_fd);
					continue;
                }

				if (no_cache) {
					// we need to define this struct since devctl fills the hdr field and then adds the path after.
					struct {
						procfs_debuginfo hdr;
						char             path[PATH_MAX];
					} dbg{};
					// dbg.hdr.vaddr = info.base_address;
					if (devctl(ctl_fd, DCMD_PROC_MAPDEBUG_BASE, &dbg, sizeof(dbg), nullptr) == EOK) {
						std::string  exe_path = dbg.hdr.path;
						if (!exe_path.empty()) {
							new_proc.name = fs::path(exe_path).filename().string();
							new_proc.cmd = exe_path;
						}else {
							new_proc.name =  "[" + std::to_string(pid) + "]" ;
						}
					}

                    new_proc.ppid  = (uint64_t)info.parent;
                    new_proc.cpu_s = (uint64_t)(Mem::old_uptime + info.start_time / 1e9);

					// fill in the username from passwd
                    uid_t uid = info.uid;
                    std::string uid_str = std::to_string(uid);
                    if (not uid_user.contains(uid_str)) {
                        struct passwd* pw = getpwuid(uid);
                        uid_user[uid_str] = pw ? pw->pw_name : uid_str;
                    }
                    new_proc.user = uid_user.at(uid_str);
                }

                new_proc.threads = info.num_threads;

				// Take the state from TID1
				procfs_status procstatus{};
				procstatus.tid = 1;
				if (devctl(ctl_fd, DCMD_PROC_TIDSTATUS, &procstatus, sizeof(procstatus), nullptr) == EOK) {
					new_proc.state = qnx_proc_states.at(procstatus.state);
				} else new_proc.state = 'U'; // If we can't get TIDSTATUS just set it to unkown

				new_proc.mem = 0;
				procfs_asinfo asinfo{};
				if (devctl(ctl_fd, DCMD_PROC_ASINFO, &asinfo, sizeof(asinfo), nullptr) == EOK) {
					new_proc.mem = asinfo.rss;
				}

				uint64_t cpu_t = info.utime + info.stime;
				uint64_t new_proc_time_ns;
				uint64_t collect_interval; 
				// handle first render differently since we don't have past data
				if (last_collect_time_ns == 0) {
					collect_interval = 1; // just so we don't divide by 0
					new_proc_time_ns = 0; // clamp at 0 for the first render so we don't spike to 10000% 
				}else {
					new_proc_time_ns = cpu_t - new_proc.cpu_t;
					collect_interval = time_now_ns - last_collect_time_ns;
				}

				new_proc.cpu_s = info.start_time;
				new_proc.cpu_p = clamp(100.0 * new_proc_time_ns / collect_interval * cmult, 0.0, 100.0 * Shared::coreCount);
				new_proc.cpu_c = (double)(cpu_t * Shared::clkTck / 1e6) / max(1.0, (double)time_now_ns - new_proc.cpu_s);
				new_proc.cpu_t = cpu_t;

                new_proc.p_nice = info.priority;
                close(ctl_fd);

                if (show_detailed and not got_detailed and new_proc.pid == detailed_pid) {
                    got_detailed = true;
				}
            }

			//? Clear dead processes from current_procs if not paused
			if (not pause_proc_list) {
				auto eraser = rng::remove_if(current_procs, [&](const auto& element) { return not v_contains(found, element.pid); });
				current_procs.erase(eraser.begin(), eraser.end());
				if (!dead_procs.empty()) dead_procs.clear();
			}
			//? Set correct state of dead processes if paused
			else {
				for (auto& r : current_procs) {
					if (rng::find(found, r.pid) == found.end()) {
						if (r.state != 'X') {
							struct timeval currentTime;
							gettimeofday(&currentTime, nullptr);
							r.death_time = currentTime.tv_sec - r.cpu_s;
						}
						r.state = 'X';
						dead_procs.emplace(r.pid);
						//? Reset cpu usage for dead processes if paused and option is set
						if (!Config::getB("keep_dead_proc_usage")) {
							r.cpu_p = 0.0;
							r.mem = 0;
						}
					}
				}
			}

			//? Update the details info box for process if active
			if (show_detailed and got_detailed) {
				_collect_details(detailed_pid, current_procs);
			} else if (show_detailed and not got_detailed and detailed.status != "Dead") {
				detailed.status = "Dead";
				redraw = true;
			}

			last_collect_time_ns = time_now_ns;
        }

        // Filter
        if (should_filter) {
            filter_found = 0;
            for (auto& p : current_procs) {
                if (not tree and not filter.empty()) {
                    p.filtered = not matches_filter(p, filter);
                    if (p.filtered) filter_found++;
                } else p.filtered = false;
            }
        }

        // Sort
        if (sorted_change or tree_mode_change or (not no_update and not pause_proc_list)) {
            proc_sorter(current_procs, sorting, reverse, tree);
		}

        // Tree view
        if (tree and (not no_update or should_filter or sorted_change)) {
            bool locate_selection = false;

            if (toggle_children != -1) {
                auto collapser = rng::find(current_procs, toggle_children, &proc_info::pid);
                if (collapser != current_procs.end()) {
                    for (auto& p : current_procs) {
                        if (p.ppid == collapser->pid) {
                            auto child = rng::find(current_procs, p.pid, &proc_info::pid);
                            if (child != current_procs.end())
                                child->collapsed = not child->collapsed;
                        }
                    }
                    if (Config::ints.at("proc_selected") > 0) locate_selection = true;
                }
                toggle_children = -1;
            }

			if (auto find_pid = (collapse != -1 ? collapse : expand); find_pid != -1) {
				auto collapser = rng::find(current_procs, find_pid, &proc_info::pid);
				if (collapser != current_procs.end()) {
					if (collapse == expand) {
						collapser->collapsed = not collapser->collapsed;
					}
					else if (collapse > -1) {
						collapser->collapsed = true;
					}
					else if (expand > -1) {
						collapser->collapsed = false;
					}
					if (Config::ints.at("proc_selected") > 0) locate_selection = true;
				}
				collapse = expand = -1;
			}
			if (should_filter or not filter.empty()) filter_found = 0;

            vector<tree_proc> tree_procs;
            tree_procs.reserve(current_procs.size());

			if (!pause_proc_list) {
				for (auto& p : current_procs) {
					if (not v_contains(found, p.ppid)) p.ppid = 0;
				}
			}

			//? Stable sort to retain selected sorting among processes with the same parent
			rng::stable_sort(current_procs, rng::less{}, & proc_info::ppid);

			//? Start recursive iteration over processes with the lowest shared parent pids
			for (auto& p : rng::equal_range(current_procs, current_procs.at(0).ppid, rng::less{}, &proc_info::ppid)) {
				_tree_gen(p, current_procs, tree_procs, 0, false, filter, false, no_update, should_filter);
			}

			//? Recursive sort over tree structure to account for collapsed processes in the tree
			int index = 0;
			tree_sort(tree_procs, sorting, reverse, (pause_proc_list and not (sorted_change or tree_mode_change)), index, current_procs.size());

			//? Recursive construction of ASCII tree prefixes.
			for (auto t = tree_procs.begin(); t != tree_procs.end(); ++t) {
				_collect_prefixes(*t, t == tree_procs.end() - 1);
			}

			//? Final sort based on tree index
			rng::stable_sort(current_procs, rng::less {}, &proc_info::tree_index);

			//? Move current selection/view to the selected process when collapsing/expanding in the tree
			if (locate_selection) {
				int loc = rng::find(current_procs, Proc::selected_pid, &proc_info::pid)->tree_index;
				if (Config::ints.at("proc_start") >= loc or Config::ints.at("proc_start") <= loc - Proc::select_max)
					Config::ints.at("proc_start") = max(0, loc - 1);
				Config::ints.at("proc_selected") = loc - Config::ints.at("proc_start") + 1;
			}
        }

        numpids = (int)current_procs.size() - filter_found;
        return current_procs;
    }
} // namespace Proc

namespace Tools {
    double system_uptime() {
        time_t bt = (time_t)SYSPAGE_ENTRY(qtime)->boot_time;
        return (double)(time(nullptr) - bt);
    }
} // namespace Tools
