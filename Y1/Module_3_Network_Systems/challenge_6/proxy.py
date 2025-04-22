#!/usr/bin/python3
import platform
#
# TCP_Hack proxy
# Update 01-12-2021: Update for compatibility with new scapy version on Windows
# Update 19-03-2022: Changes to errors and instructions to make usage clearer. Updates for better interface handling on Linux
#
# Tested using scapy 2.4.5 (latest at time of writing) and 2.4.0

print("==== Network Systems TCP hack proxy ====")

import argparse
## argument parsing
parser = argparse.ArgumentParser(description='Proxy for the TCPHack challenge. Will selfconfigure in most cases. You should only choose an interface if it does not work automatically.')
parser.add_argument("-i", "--interface", help="Interface name to proxy on", type=str, required=False)
parser.add_argument("-ii", "--interface-index", help="Index of interface to listen on (Takes priority over --interface)", type=int, required=False)
parser.add_argument("-l", "--list", help="Prints a list of all IPv6 capable interfaces and exits", action="store_true")
parser.add_argument("-c", "--choose", help="Prints a list of all IPv6 capable interfaces and lets you choose which to use", action="store_true")
parser.add_argument("-st", "--skip-tests", help="Skips connection tests.", action="store_true")
args = parser.parse_args()

print("Starting TCPHack proxy.\nPlease wait, this might take a few seconds...\n(Seriously, just keep waiting)")

import sys
try:
    from scapy.all import *                   
except ImportError:
    print("Error: Failed to import scapy!")
    if platform.system() == 'Windows':
        print("You can install scapy using pip (assuming python3 pip, might need to use pip3): 'pip install scapy' or 'python -m pip install scapy'.")
    else:
        print("You can likely find scapy with your package manager, the package will likely have a name like 'python3-scapy'.")
        print("Alternatively you can install scapy using pip: 'pip3 install scapy --user' or 'python3 -m pip install scapy --user', but using your package manager is recommended.")
        print("If you keep getting this error after installing scapy using the package manager, please remove it and try using pip!")
    sys.exit(1)
from socket import *
from struct import *
from threading import Thread
import os
import time

if platform.system() == 'Windows': from scapy.arch.windows import get_windows_if_list
if platform.system() == 'Darwin': conf.use_pcap = True
print("============= Loading done =============\n")

# Warning: you should NOT change these addresses!
TEST_IP = "2001:67c:2564:a173:250:56ff:fe85:619b"
TEST_253_IP = "2001:67c:2564:ab10:7cfe:7a02:6e96:d5f3"
CHALLENGE_NET = "2001:67c:2564:ab10::0/64"
LISTEN_IP = "127.0.0.1"
LISTEN_PORT = 1234
RECV_BUFFER = 1024

class clientSock:
    def __init__(self):
        self.sock = None
clientsock = clientSock()

is_tun = False
own_ip = None
chosen_interface_name = None
chosen_interface_mac = None

if args.interface or args.interface_index or args.list or args.choose: # We need to list all interfaces
    nics = []
    if platform.system() == 'Windows': # special Windows stuff
        nic_list = get_windows_if_list()
        for nic in nic_list:
            name = nic['name']
            index = nic['index']
            if_hw_addr = None
            try:
                # if_hw_addr = get_if_hwaddr(name)
                if_hw_addr = nic['mac']
            except:
                pass
            ip6_addr = None
            try:
                ip6_addr = get_if_addr6(ifaces.dev_from_index(index))
                # print(nic['ips'], get_if_addr6(ifaces.dev_from_index(index)))
                # ip6_addr = nic['ips'][0]
            except:
                pass
            if ip6_addr is not None:
                nics.append( [index, name, if_hw_addr, ip6_addr] )
    else: # Assume Linux and macOS are the same...
        nic_list = get_if_list()
        for nic in nic_list:
            try: 
                if_index = get_if_index(nic) # deal with older scapy versions
            except NameError:
                if_index = dev_from_networkname(nic).index # new method
            if_hw_addr = None
            try:
                if_hw_addr = get_if_hwaddr(nic)
            except:
                pass
            ip6_addr = get_if_addr6(nic)
            if ip6_addr is not None:
                nics.append( [if_index, nic, if_hw_addr, ip6_addr] )

    def list_interfaces():
        if len(nics) == 0:
            print("No IPv6 capable interfaces found! Please check if you have IPv6 connectivity.")
            sys.exit(1)
        max_len = 14
        for nic in nics:
            if len(nic[1]) > max_len: max_len = len(nic[1])
        print("IPv6 capable interfaces with globally routable addresses found:")
        print("id | {} |               mac | IPv6 address".format("Interface name".rjust(max_len)))
        print("-----------------------------------------"+"-"*max_len)
        for nic in nics:
            temp_mac = ""
            if nic[2] is not None:
                temp_mac = nic[2]
            print("{:2} | {} | {:13} | {}".format(nic[0], nic[1].rjust(max_len), temp_mac.rjust(17), nic[3]))

    if args.list:
        list_interfaces()
        sys.exit(0)

    if args.interface:
        for nic in nics:
            if nic[1] == args.interface:
                chosen_interface_name = nic[1]
                own_ip = nic[3]
                break

    if args.interface_index:
        for nic in nics:
            if args.interface_index == nic[0]:
                chosen_interface_name = nic[1]
                own_ip = nic[3]
                break

    if args.choose:
        list_interfaces()
        index_choice = input("Interface id: ")
        try:
            index_choice = int(index_choice)
        except:
            print("That is not a valid interface id!")
            sys.exit(1)
        for nic in nics:
            if nic[0] == index_choice:
                chosen_interface_name = nic[1]
                own_ip = nic[3]
                break        
    
    if chosen_interface_name is None: # exit if input was an unknown interface
        print("Unknown interface chosen!")
        sys.exit(1)

    print(" - IPv6 capable interface chosen by user!")
    
else: # auto configure proxy
    if conf.iface6 is None:
        print(" - Error: Could not automatically find IPv6 capable interface, please confirm you have IPv6 connectivity!")
        print("   If you do not have IPv6 connectivity on your internet connection you can use EduVPN to get an IPV6 capable tunnel.")
        print("   You can run the proxy with '-h' to get more instructions on manually selecting an interface.")
        sys.exit(1)   
    if type(conf.iface6) == str: # (older) scapy version on Linux / macOS
        chosen_interface_name = conf.iface6
    else: # Scapy on Windows and newer scapy version on Linux / macOS
        chosen_interface_name = conf.iface6.name
    own_ip = get_if_addr6(conf.iface6)
    print('Your IPv6 address: {}'.format(own_ip))
    if own_ip is None or not scapy.utils6.in6_isgladdr( own_ip ):
        print(" - Error: Could not automatically find IPv6 capable interface with an address in the globally routable address space!")
        print("   If you do not have IPv6 connectivity on your internet connection you can use EduVPN to get an IPV6 capable tunnel.")
        print("   If you do and automatic detection failed please select the interface yourself by running the proxy with '-c'.")
        print("   You can run the proxy with '-h' to get more instructions on manually selecting an interface.")
        sys.exit(1)   
    # detect loopback interface and notify user
    if chosen_interface_name == 'lo':
        print(" - Error: The automatic configuration selected the loopback interface!")
        print("   Please select the interface yourself by running the proxy with '-c'.")
        print("   You can run the proxy with '-h' to get more instructions.")
        sys.exit(1)
    print(" - Found IPv6 capable interface!")

try:
    chosen_interface_mac = get_if_hwaddr(chosen_interface_name)
    print("   Using interface:",chosen_interface_name, "with mac:", chosen_interface_mac )
except:
    is_tun = True
    pass

# Something changed in scapy or linux network stack so get_if_hwaddr no longer fails on layer 3 tunnel;s
if chosen_interface_mac == '00:00:00:00:00:00':
    is_tun = True

if is_tun:
    chosen_interface_mac = ""
    is_tun = True
    print(" - Detected layer 3 tunnel.")
    print("   Using interface:",chosen_interface_name )

print("   Your IPv6 address: {}".format(own_ip))

# Try to find gateway mac using scapy's neighbor info
if is_tun:
    next_hop_mac = ""
else:
    pkt = Ether()/IPv6(src=own_ip, dst=TEST_IP)
    try:
        next_hop_mac = conf.neighbor.resolve(pkt, pkt.payload)
    except PermissionError:
        print("Error: need extra permissions to perform capture, please run using sudo!")
        sys.exit(1)
    if next_hop_mac == "ff:ff:ff:ff:ff:ff" or next_hop_mac is None: # Find gateway by waiting for a Router Advertisement
        print("   Warning: Could not find gateway mac, waiting for Router Advertisement, this could also take a few (or 30) seconds...")
        packets = sniff(filter="icmp6 && ip6[40] == 134", count=1, iface=chosen_interface_name)
        next_hop_mac = packets[0].src
    print("   Using gateway mac:", next_hop_mac )

# In some cases Windows might not give correct information to scapy... Super rare, can't accurately reproduce
# This whole part might not be needed with newer scapy versions...
if platform.system() == 'Windows' and len( conf.route6.routes ) == 0:
    print(" - Could not find IPv6 routes, starting automatic search...")

    netstat = os.popen("netstat -nr")
    in_if_list = False
    in_ipv6_routes = False
    interface_list = dict()
    gateway_ip = -1
    if_to_gateway = -1
    for entry in netstat:
        if in_if_list:
            if "=====" in entry: # at end of if list
                in_if_list = False
            else:
                parts = entry.split('.')
                # print(parts)
                if_id = int( parts[0] )
                if_name = parts[-1][:-1] # remove new line
                if_mac = parts[3][:-1] #last char is a space...
                interface_list[ if_id ] = (if_name, if_mac)

        if in_ipv6_routes and "::/0" in entry: # this is the global route
            # print( entry.split() )
            gateway_ip = entry.split()[3]
            if_to_gateway = int( entry.split()[0] )
            break

        if "Interface List" in entry: in_if_list = True
        if "IPv6 Route Table" in entry: in_ipv6_routes = True
    if if_to_gateway == -1:
        print("   Error: Could not find an IPv6 route...\n   Is IPv6 enabled on your system?")
        sys.exit(1)

    router_mac = -1
    neighbors = os.popen("netsh int ipv6 show neigh interface="+str(if_to_gateway))
    for entry in neighbors:
        # print("Possible next hop: ", entry)
        if gateway_ip in entry and "Reachable (Router)" in entry:
            router_mac = entry.split()[1]
            # print(entry, router_mac)

    if router_mac == -1:
        print("   Error: Could not find the mac address for the next hop router, this should never happen")
        sys.exit(2)
    
    chosen_interface_name = interface_list[if_to_gateway][0]
    chosen_interface_mac = interface_list[if_to_gateway][1].replace(" ",":")
    next_hop_mac = router_mac.replace("-",":")
    print("   Using interface:",interface_list[if_to_gateway][0])

class SniffThread(Thread):
    SNIFF_FILTER = "ip6 and src net " + CHALLENGE_NET + " and not src " + TEST_253_IP

    def __init__ (self, cb, clientsock):
        self.__cb = cb
        self.clientsock = clientsock
        Thread.__init__(self)

    def run(self):
        sniff(filter=self.SNIFF_FILTER, prn=self.callback, iface=chosen_interface_name)

    def callback(self, p):
        if IPv6 in p:
            self.__cb(p, self.clientsock)
            print("Packet sniffed")

class CommunicationThread(Thread):
    clients = []
    current_sock = None

    def __init__(self, clientsock,  *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.clientsock = clientsock

    def run(self):
        serversock = socket(AF_INET, SOCK_STREAM)
        serversock.setsockopt(SOL_SOCKET, SO_REUSEADDR, 1)
        serversock.bind((LISTEN_IP, LISTEN_PORT))
        serversock.listen(5)

        while True:
            # Connect a client and set it as the current client
            print("You can keep this proxy running, no need to restart it for every run!")
            print("Waiting for client...")
            sock, addr = serversock.accept()
            self.current_sock = sock
            clientsock.sock = sock
  
            t = CommunicationClient(sock, addr, daemon=True)
            # t.setDaemon(True)
            t.start()

            # Kill all of the other clients
            for c in self.clients[:]:
                try:
                    c.kill()
                    c.join()
                except Exception as e:
                    print("Could not stop old client properly: {}".format(e))
                self.clients.remove(c)

            # Add the new one to the list
            self.clients.append(t)

class CommunicationClient(Thread):
    run = True
    sock = None
    client_id = None

    def __init__(self, sock, addr, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.sock = sock
        self.client_id = addr

    def kill(self):
        # Try to gracefully kill this client connection
        self.run = False
        try:
            self.sock.shutdown(1)
            self.sock.close()
        except Exception as e:
            print("Could not close socket properly: {}".format(e))
        self.sock = None
        print("Client {} disconnected!".format(self.client_id))

    def run(self):
        print("Client {} connected!".format(self.client_id))
        data_so_far = br""

        while True:
            try:
                data = self.sock.recv(RECV_BUFFER)
                if len(data) == 0: break
            except Exception as e:
                if self.run:
                    print("Could not receive data from client: {}".format(e))
                break
            data_so_far += data

            while len(data_so_far) >= 4:
                n, = unpack(">i", data_so_far[:4])
                if len(data_so_far) >= (n + 4):
#                       print("Sending packet of " + str(n) + " bytes, data left: " + str(len(data_so_far) - (n + 4)))
                    print("Sending packet of " + str(n) + " bytes")
                    put_packet_on_wire(data_so_far[4:n+4])
                    data_so_far = data_so_far[n+4:]
                else:
                    break

        if self.sock is not None:
            try:
                self.sock.close()
            except Exception as e:
                print("Could not close socket properly: {}".format(e))
            print("Client {} disconnected!".format(self.client_id))
            print("You can leave this running to wait for another client.")


def put_packet_on_wire(data):
    if is_tun:
        sendp( IPv6(data), verbose=9, iface=chosen_interface_name )
    else:
        sendp( Ether(src=chosen_interface_mac,dst=next_hop_mac)/IPv6(data), verbose=9, iface=chosen_interface_name )

def packet_sniffed(p,clientsock):
    packetstring = bytes(p[IPv6])
    if clientsock.sock is not None:
        try:
            length = pack(">i", len(packetstring))
            clientsock.sock.send(length + packetstring)
        except Exception as e:
            print("Could not send sniffed packet to client: {}".format(e))


version_too_old = False
try:
    scapy_version = [int(i) for i in conf.version.split('.')]
    if scapy_version[0] < 2:
        version_too_old = True
    elif scapy_version[0] == 2 and scapy_version[1] < 4:
        version_too_old = True
    elif scapy_version[0] == 2 and scapy_version[1] == 4 and scapy_version[2] < 3:
        version_too_old = True
except:
    print("\n - Warning: Failed check of scapy version, if the proxy crashes on the tests please re-run with -st to skip tests...")
    pass

if args.skip_tests or version_too_old:
    print("\n - Skipping connection tests...\n")
    if version_too_old:
        print("   Scapy version needs to be at least 2.4.3 for AsyncSniffer")
else:
    # Test ipv6 connection
    tests_failed = 0
    p = []
    sniffer = AsyncSniffer(filter="icmp6 and ip6[40] == 129 and src "+TEST_IP, iface=chosen_interface_name)
    sniffer.start()
    print("\n - Starting ping test to challenge server...")
    time.sleep(1) # give capture time to start so we don't miss fast replies
    if is_tun:
        sendp( [IPv6(dst=TEST_IP, src=own_ip)/ICMPv6EchoRequest() for i in range(4)], verbose=0, iface=chosen_interface_name )
    else:
        sendp( [Ether(src=chosen_interface_mac,dst=next_hop_mac)/IPv6(dst=TEST_IP, src=own_ip)/ICMPv6EchoRequest() for i in range(4)], verbose=0, iface=chosen_interface_name )
    time.sleep(2) # wait a bit so we can get a response
    p = sniffer.stop()
    if len(p) == 0:
        print("   Failed to ping challenge server. Please make sure you have IPv6 connectivity!\n")
        tests_failed += 1
    else:
        print("   Challenge server is reachable over IPv6! {}/{} echos received.\n".format(len(p),4))

    # Test TCP syn on port 80 to 'normal' challenge server IP
    p = []
    sniffer = AsyncSniffer(filter="ip6 and src port 80 and src "+TEST_IP, iface=chosen_interface_name)
    sniffer.start()
    tcp_test_80 = TCP(sport=6789, dport=80)
    print(" - Starting 'normal' TCP test to challenge server...")
    time.sleep(1) # give capture time to start so we don't miss fast replies
    if is_tun:
        sendp( IPv6(dst=TEST_IP, src=own_ip)/tcp_test_80, verbose=0, iface=chosen_interface_name )
    else:
        sendp( Ether(src=chosen_interface_mac,dst=next_hop_mac)/IPv6(dst=TEST_IP, src=own_ip)/tcp_test_80, verbose=0, iface=chosen_interface_name )
    time.sleep(2) # wait a bit so we can get a response
    p = sniffer.stop()
    if len(p) == 0:
        print("   Failed TCP test to challenge server! This could indicate a routing issue...\n")
        tests_failed += 1
    else:
        print("   Challenge server is reachable by TCP!\n")

    p = []
    sniffer = AsyncSniffer(filter="ip6 and src "+TEST_253_IP, iface=chosen_interface_name)
    sniffer.start()
    tcp_test_7710 = IPv6(dst=TEST_253_IP, src=own_ip , nh=253)/TCP(sport=6789, dport=7710)
    print(" - Starting next header 253 test to challenge server...")
    time.sleep(1) # give capture time to start so we don't miss fast replies
    if is_tun:
        sendp( tcp_test_7710, verbose=0, iface=chosen_interface_name)
    else:
        sendp( Ether(src=chosen_interface_mac,dst=next_hop_mac)/tcp_test_7710, verbose=0, iface=chosen_interface_name)
    time.sleep(2) # wait a bit so we can get a response
    p = sniffer.stop()
    if len(p) == 0:
        print("   Failed next header 253 test to challenge server! There might be something in your network blocking 253 packets...\n")
        tests_failed += 1
    else:
        print("   Challenge server is reachable with next header 253!\n")

    # Handle failed tests. Students can choose to ignore these warnings in case they are caused by restrive firewalls and/or specific routes they use for the challenge.
    if tests_failed > 0:
        print(" - Warning: one or more connectivity tests failed!")
        print("   This could indicate it is not possible to do the challenge in your current network environment.")
        print("   You should ask a TA to help you or you can choose to ignore this warning and continue by entering 'Y'.")
        response = input("continue (y/N)?: ")
        if response.strip().lower() != "y":
            sys.exit(1)

# Start proxy
commsthread = CommunicationThread(clientsock)
commsthread.daemon = True
commsthread.start()

sniffthread = SniffThread(packet_sniffed, clientsock)
sniffthread.daemon = True
sniffthread.start()

while True:
    time.sleep(1)

