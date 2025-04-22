#include "client.hpp"
#include <time.h>
#include <unistd.h>
#if defined _MSC_VER || defined __MINGW32__ || defined __CYGWIN__
#include <Winsock2.h>
#endif

#include <stdlib.h>
#include <time.h>
#include <stdio.h>
#include <inttypes.h>
#include <cstdint>
#include <cstring>
#include <string>
#include <netinet/in.h>
#include <chrono>
#include <thread>

#define RETRANSMITS 10

uint16_t calculate_tcp_checksum(unsigned char* packet, int tcp_length) {
    struct {
        uint8_t src_addr[16];
        uint8_t dst_addr[16];
        uint32_t tcp_length;
        uint8_t zeros[3];
        uint8_t next_header;
    } pseudo_header;

    memcpy(pseudo_header.src_addr, &packet[8], 16);
    memcpy(pseudo_header.dst_addr, &packet[24], 16);
    pseudo_header.tcp_length = htonl(tcp_length);
    memset(pseudo_header.zeros, 0, 3);
    pseudo_header.next_header = 253;

    uint16_t original_checksum = (packet[56] << 8) | packet[57];

    packet[56] = 0;
    packet[57] = 0;

    uint32_t sum = 0;

    uint16_t* ptr = (uint16_t*)&pseudo_header;
    for (int i = 0; i < sizeof(pseudo_header)/2; i++) {
        sum += ntohs(ptr[i]);
    }

    ptr = (uint16_t*)&packet[40];
    for (int i = 0; i < tcp_length/2; i++) {
        sum += ntohs(ptr[i]);
    }

    if (tcp_length % 2) {
        sum += (packet[40 + tcp_length - 1] << 8);
    }

    while (sum >> 16) {
        sum = (sum & 0xFFFF) + (sum >> 16);
    }

    uint16_t checksum = ~sum;

    packet[56] = original_checksum >> 8;
    packet[57] = original_checksum & 0xFF;

    return checksum;
}

void build_ipv6_header(unsigned char* packet, uint16_t payload_length, uint16_t dest_port) {
    packet[0] = 0x60;
    packet[1] = 0x00;
    packet[2] = 0x00;
    packet[3] = 0x00;
    packet[4] = (payload_length >> 8) & 0xFF;
    packet[5] = payload_length & 0xFF;
    packet[6] = 253;
    packet[7] = 64;

    // Source address
    packet[8] = 0x00;  packet[9] = 0x00;
    packet[10] = 0x00; packet[11] = 0x00;
    packet[12] = 0x00; packet[13] = 0x00;
    packet[14] = 0x00; packet[15] = 0x00;
    packet[16] = 0x00; packet[17] = 0x00;
    packet[18] = 0x00; packet[19] = 0x00;
    packet[20] = 0x00; packet[21] = 0x00;
    packet[22] = 0x00; packet[23] = 0x00;

    // Destination address
    packet[24] = 0x00; packet[25] = 0x00;
    packet[26] = 0x00; packet[27] = 0x00;
    packet[28] = 0x00; packet[29] = 0x00;
    packet[30] = 0x00; packet[31] = 0x00;
    packet[32] = 0x00; packet[33] = 0x00;
    packet[34] = 0x00; packet[35] = 0x00;
    packet[36] = 0x00; packet[37] = 0x00;
    packet[38] = 0x00; packet[39] = 0x00;
}

uint32_t parse_uint32(unsigned char* data) {
    return (uint32_t)(data[0] << 24 | data[1] << 16 | data[2] << 8 | data[3]);
}

uint32_t get_seq_num(unsigned char* packet) {
    return parse_uint32(&packet[44]);
}

uint32_t get_ack_num(unsigned char* packet) {
    return parse_uint32(&packet[48]);
}

int main(void) {
#if defined _MSC_VER || defined __MINGW32__ || defined __CYGWIN__
    WSADATA wsaDataUnused;
    WSAStartup(/*version*/2, &wsaDataUnused);
#endif

    connect();

//    uint16_t ports[] = {7710, 7711, 7712, 7713};

retry:

    uint16_t ports[6] = {7713, 7713, 7713, 7713, 7713, 7713};

    for (int port_idx = 0; port_idx < 6; port_idx++) {

        uint16_t current_port = ports[port_idx];
        printf("\n=== Trying port %d ===\n", current_port);

        bool connection_established = false;
        bool http_request_sent = false;
        bool data_received = false;
        std::string received_data = "";

        uint32_t client_seq_num = rand() % 0xFFFFFFFF;
        uint32_t server_seq_num = 0;
        uint32_t next_ack_num = 0;

        int retries = 0;
        const int max_retries = 100;

        unsigned char txpkt[1500];

        memset(txpkt, 0, sizeof(txpkt));
        uint16_t payload_len = 20;

        build_ipv6_header(txpkt, payload_len, current_port);

        uint16_t src_port = 49152 + port_idx;
        txpkt[40] = (src_port >> 8) & 0xFF;
        txpkt[41] = src_port & 0xFF;

        txpkt[42] = (current_port >> 8) & 0xFF;
        txpkt[43] = current_port & 0xFF;

        txpkt[44] = (client_seq_num >> 24) & 0xFF;
        txpkt[45] = (client_seq_num >> 16) & 0xFF;
        txpkt[46] = (client_seq_num >> 8) & 0xFF;
        txpkt[47] = client_seq_num & 0xFF;

        txpkt[48] = 0x00;
        txpkt[49] = 0x00;
        txpkt[50] = 0x00;
        txpkt[51] = 0x00;

        txpkt[52] = 0x50;
        txpkt[53] = 0x02;

        uint16_t window_size = 64240;
        txpkt[54] = (window_size >> 8) & 0xFF;
        txpkt[55] = window_size & 0xFF;

        txpkt[56] = 0x00;
        txpkt[57] = 0x00;

        txpkt[58] = 0x00;
        txpkt[59] = 0x00;

        uint16_t checksum = calculate_tcp_checksum(txpkt, payload_len);
        txpkt[56] = (checksum >> 8) & 0xFF;
        txpkt[57] = checksum & 0xFF;

        printf("Sending SYN packet to port %d...\n", current_port);
        send(txpkt, 60);

        time_t last_send_time = time(NULL);

        while (!data_received && retries < max_retries) {
            unsigned char *rxpkt = receive(1000);

            if (!rxpkt) {
                time_t current_time = time(NULL);
                if (current_time - last_send_time >= 2) {
                    if (!connection_established) {
                        printf("Timeout waiting for SYN-ACK, retrying...\n");
                        //send(txpkt, 60);
                        goto retry;

//                        if (current_port == 7713) {
//                            for (int i = 0; i < RETRANSMITS; i++) {
//                                std::this_thread::sleep_for(std::chrono::milliseconds(200));
//                                send(txpkt, 60);
//                            }
//                        }

                    } else if (!http_request_sent) {
                        printf("Timeout waiting for HTTP response, retransmitting HTTP request...\n");
                        send(txpkt, 60 + strlen("GET / HTTP/1.0\r\n\r\n"));

                        if (current_port == 7713) {
                            printf("Sending HTTP request...\n");
                            for (int i = 0; i < RETRANSMITS; i++) {
                                std::this_thread::sleep_for(std::chrono::milliseconds(200));
                                send(txpkt, 60 + strlen("GET / HTTP/1.0\r\n\r\n"));
                            }
                        }
                    }
                    last_send_time = current_time;
                    retries++;
                }
                continue;
            }

            int len = get_received_length();

            printf("Received %i bytes: ", len);
            for (int i = 0; i < 60 && i < len; i++) {
                printf("%02x ", rxpkt[i]);
            }
            printf("\n");

            uint8_t flags = rxpkt[53];

            if (!connection_established && (flags & 0x12) == 0x12) {
                printf("Received SYN-ACK. Sending ACK...\n");

                server_seq_num = get_seq_num(rxpkt);
                uint32_t ack_of_our_syn = get_ack_num(rxpkt);

                if (ack_of_our_syn != client_seq_num + 1) {
                    printf("Warning: Server acknowledged unexpected sequence number\n");
                }

                memset(txpkt, 0, sizeof(txpkt));

                build_ipv6_header(txpkt, 20, current_port);

                txpkt[40] = (src_port >> 8) & 0xFF;
                txpkt[41] = src_port & 0xFF;
                txpkt[42] = (current_port >> 8) & 0xFF;
                txpkt[43] = current_port & 0xFF;

                client_seq_num = ack_of_our_syn;
                txpkt[44] = (client_seq_num >> 24) & 0xFF;
                txpkt[45] = (client_seq_num >> 16) & 0xFF;
                txpkt[46] = (client_seq_num >> 8) & 0xFF;
                txpkt[47] = client_seq_num & 0xFF;

                next_ack_num = server_seq_num + 1;
                txpkt[48] = (next_ack_num >> 24) & 0xFF;
                txpkt[49] = (next_ack_num >> 16) & 0xFF;
                txpkt[50] = (next_ack_num >> 8) & 0xFF;
                txpkt[51] = next_ack_num & 0xFF;

                txpkt[52] = 0x50;
                txpkt[53] = 0x10;

                txpkt[54] = (window_size >> 8) & 0xFF;
                txpkt[55] = window_size & 0xFF;

                txpkt[56] = 0x00;
                txpkt[57] = 0x00;

                txpkt[58] = 0x00;
                txpkt[59] = 0x00;

                checksum = calculate_tcp_checksum(txpkt, 20);
                txpkt[56] = (checksum >> 8) & 0xFF;
                txpkt[57] = checksum & 0xFF;

                send(txpkt, 60);

                if (current_port == 7713) {
                    for (int i = 0; i < RETRANSMITS; i++) {
                        std::this_thread::sleep_for(std::chrono::milliseconds(200));
                        send(txpkt, 60);

                    }
                }

                connection_established = true;
                last_send_time = time(NULL);

                memset(txpkt, 0, sizeof(txpkt));

                const char* http_request = "GET / HTTP/1.0\r\n\r\n";
                int http_len = strlen(http_request);
                uint16_t payload_len = 20 + http_len;

                build_ipv6_header(txpkt, payload_len, current_port);

                txpkt[40] = (src_port >> 8) & 0xFF;
                txpkt[41] = src_port & 0xFF;
                txpkt[42] = (current_port >> 8) & 0xFF;
                txpkt[43] = current_port & 0xFF;

                txpkt[44] = (client_seq_num >> 24) & 0xFF;
                txpkt[45] = (client_seq_num >> 16) & 0xFF;
                txpkt[46] = (client_seq_num >> 8) & 0xFF;
                txpkt[47] = client_seq_num & 0xFF;

                txpkt[48] = (next_ack_num >> 24) & 0xFF;
                txpkt[49] = (next_ack_num >> 16) & 0xFF;
                txpkt[50] = (next_ack_num >> 8) & 0xFF;
                txpkt[51] = next_ack_num & 0xFF;

                txpkt[52] = 0x50;
                txpkt[53] = 0x18;

                txpkt[54] = (window_size >> 8) & 0xFF;
                txpkt[55] = window_size & 0xFF;

                txpkt[56] = 0x00;
                txpkt[57] = 0x00;

                txpkt[58] = 0x00;
                txpkt[59] = 0x00;

                memcpy(&txpkt[60], http_request, http_len);

                checksum = calculate_tcp_checksum(txpkt, payload_len);
                txpkt[56] = (checksum >> 8) & 0xFF;
                txpkt[57] = checksum & 0xFF;

                printf("Sending HTTP request...\n");
                send(txpkt, 60 + http_len);

                if (current_port == 7713) {
                    for (int i = 0; i < RETRANSMITS; i++) {
                        printf("Sending HTTP request... %d \n", i + 1);
                        std::this_thread::sleep_for(std::chrono::milliseconds(200));
                        send(txpkt, 60 + http_len);
                    }
                }

                http_request_sent = true;
                last_send_time = time(NULL);
                client_seq_num += http_len;

            }
            else if (connection_established && (flags & 0x10)) {  // ACK flag
                int tcp_header_len = ((rxpkt[52] & 0xF0) >> 4) * 4;
                int data_start = 40 + tcp_header_len;
                int data_len = len - data_start;

                if (data_len > 0) {
                    printf("Received data packet (%d bytes of data)\n", data_len);

                    for (int i = data_start; i < len; i++) {
                        received_data += (char)rxpkt[i];
                    }

                    uint32_t packet_seq = get_seq_num(rxpkt);
                    next_ack_num = packet_seq + data_len;

                    memset(txpkt, 0, sizeof(txpkt));

                    build_ipv6_header(txpkt, 20, current_port);

                    txpkt[40] = (src_port >> 8) & 0xFF;
                    txpkt[41] = src_port & 0xFF;
                    txpkt[42] = (current_port >> 8) & 0xFF;
                    txpkt[43] = current_port & 0xFF;

                    txpkt[44] = (client_seq_num >> 24) & 0xFF;
                    txpkt[45] = (client_seq_num >> 16) & 0xFF;
                    txpkt[46] = (client_seq_num >> 8) & 0xFF;
                    txpkt[47] = client_seq_num & 0xFF;

                    txpkt[48] = (next_ack_num >> 24) & 0xFF;
                    txpkt[49] = (next_ack_num >> 16) & 0xFF;
                    txpkt[50] = (next_ack_num >> 8) & 0xFF;
                    txpkt[51] = next_ack_num & 0xFF;

                    txpkt[52] = 0x50;
                    txpkt[53] = 0x10;

                    txpkt[54] = (window_size >> 8) & 0xFF;
                    txpkt[55] = window_size & 0xFF;

                    txpkt[56] = 0x00;
                    txpkt[57] = 0x00;

                    txpkt[58] = 0x00;
                    txpkt[59] = 0x00;

                    checksum = calculate_tcp_checksum(txpkt, 20);
                    txpkt[56] = (checksum >> 8) & 0xFF;
                    txpkt[57] = checksum & 0xFF;

                    send(txpkt, 60);

//                    if (current_port == 7713) {
//                        printf("Sending HTTP request...\n");
//                        for (int i = 0; i < RETRANSMITS; i++) {
//                            std::this_thread::sleep_for(std::chrono::milliseconds(200));
//                            send(txpkt, 60);
//                        }
//                    }

                    if (flags & 0x01) {
                        printf("Received FIN. Connection closing.\n");
                        if (received_data.size()) {
                            data_received = true;
                        }
                    }
                }
                else if (flags & 0x01) {
                    printf("Received FIN. Sending FIN-ACK...\n");

                    memset(txpkt, 0, sizeof(txpkt));

                    build_ipv6_header(txpkt, 20, current_port);

                    txpkt[40] = (src_port >> 8) & 0xFF;
                    txpkt[41] = src_port & 0xFF;
                    txpkt[42] = (current_port >> 8) & 0xFF;
                    txpkt[43] = current_port & 0xFF;

                    txpkt[44] = (client_seq_num >> 24) & 0xFF;
                    txpkt[45] = (client_seq_num >> 16) & 0xFF;
                    txpkt[46] = (client_seq_num >> 8) & 0xFF;
                    txpkt[47] = client_seq_num & 0xFF;

                    uint32_t server_seq = get_seq_num(rxpkt);
                    next_ack_num = server_seq + 1;
                    txpkt[48] = (next_ack_num >> 24) & 0xFF;
                    txpkt[49] = (next_ack_num >> 16) & 0xFF;
                    txpkt[50] = (next_ack_num >> 8) & 0xFF;
                    txpkt[51] = next_ack_num & 0xFF;

                    txpkt[52] = 0x50;
                    txpkt[53] = 0x11;

                    txpkt[54] = (window_size >> 8) & 0xFF;
                    txpkt[55] = window_size & 0xFF;

                    txpkt[56] = 0x00;
                    txpkt[57] = 0x00;

                    txpkt[58] = 0x00;
                    txpkt[59] = 0x00;

                    checksum = calculate_tcp_checksum(txpkt, 20);
                    txpkt[56] = (checksum >> 8) & 0xFF;
                    txpkt[57] = checksum & 0xFF;

                    send(txpkt, 60);

                    if (current_port == 7713) {
                        for (int i = 0; i < RETRANSMITS; i++) {
                            std::this_thread::sleep_for(std::chrono::milliseconds(200));
                            send(txpkt, 60);
                        }
                    }

                    if (received_data.size()) {
                        data_received = true;
                    }
                }
            }
        }

        if (data_received) {
            printf("\n==== HTTP Response from port %d ====\n", current_port);
            printf("%s\n", received_data.c_str());

            size_t pos = received_data.find("secret phrase");
            if (pos != std::string::npos) {
                std::string context = received_data.substr(pos - 30, 100);
                printf("\nFound secret phrase context: %s\n", context.c_str());
            }

            printf("==== End of HTTP Response ====\n\n");
        } else {
            printf("Failed to complete TCP connection or receive data on port %d after %d retries\n",
                   current_port, max_retries);
        }
    }

#if defined _MSC_VER || defined __MINGW32__ || defined __CYGWIN__
    WSACleanup();
#endif

    return 0;
}
