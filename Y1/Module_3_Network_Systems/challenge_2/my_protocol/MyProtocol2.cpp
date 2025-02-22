///**
// * MyProtocol.cpp
// *
// *   Version: 2016-02-11
// *    Author: Jaco ter Braak & Frans van Dijk, University of Twente.
// * Copyright: University of Twente, 2015-2025
// *
// **************************************************************************
// *                          = Copyright notice =                          *
// *                                                                        *
// *            This file may  ONLY  be distributed UNMODIFIED              *
// * In particular, a correct solution to the challenge must  NOT be posted *
// * in public places, to preserve the learning effect for future students. *
// **************************************************************************
// */
//
//#include "MyProtocol.h"
//
//#include <algorithm>
//#include <chrono>
//#include <thread>
//
//namespace my_protocol {
//
//    constexpr int64_t timeout_for_sending_in_ms { 450 };
//
//    int32_t MyProtocol::calculateNumberOfPackets(const std::vector<int32_t>& fileContents) {
//        return (fileContents.size() % DATASIZE) ?
//               (fileContents.size() / DATASIZE + 1) :
//               (fileContents.size() / DATASIZE);
//    }
//
//    void MyProtocol::populatePacket(std::vector<std::vector<int32_t>>& packetsVector, const std::vector<int32_t>& fileContents) {
//        uint32_t filePointer = 0;
//        int32_t packetNumber = 1;
//
//        for (std::size_t i = 0; i < packetsVector.size(); i++) {
//            uint32_t datalen = std::min(DATASIZE, (uint32_t)fileContents.size() - filePointer);
//            packetsVector[i] = std::vector<int32_t>(HEADERSIZE + datalen);
//            numberToBigEndian(packetNumber, packetsVector[i]);
//            packetNumber++;
//
//            for (std::size_t j = HEADERSIZE; j < HEADERSIZE + datalen; j++) {
//                packetsVector[i][j] = fileContents[filePointer++];
//            }
//        }
//    }
//
//    bool MyProtocol::waitForAcknowledgement(std::vector<int32_t>& acknowledgedPacket,
//                                       std::chrono::system_clock::time_point startTime,
//                                       std::chrono::milliseconds timeDuration) {
//        while (!networkLayer->receivePacket(&acknowledgedPacket)) {
//            std::this_thread::sleep_for(std::chrono::milliseconds(10));
//            if (std::chrono::system_clock::now() - startTime > timeDuration) {
//                return false;
//            }
//        }
//        return true;
//    }
//
//    bool MyProtocol::findNextUnacknowledgedPacket(const std::vector<bool>& acknowledgedPackets, int32_t& nextPacketToSend) {
//        for (std::size_t j = 0; j < acknowledgedPackets.size(); j++) {
//            if (!acknowledgedPackets[j]) {
//                nextPacketToSend = j;
//                return false;
//            }
//        }
//        return true;
//    }
//
//    void MyProtocol::sendAcknowledgement(int32_t packetNumber) {
//        std::vector<int32_t> acknowledgedPacket(1);
//        acknowledgedPacket[0] = packetNumber;
//        networkLayer->sendPacket(acknowledgedPacket);
//    }
//
//    bool MyProtocol::checkPacketsComplete(const std::vector<std::vector<int32_t>>& packets) {
//        for (const auto& packet : packets) {
//            if (packet.size() == 0) return false;
//        }
//        return true;
//    }
//
//    std::vector<int32_t> MyProtocol::assembleFileContents(const std::vector<std::vector<int32_t>>& packets) {
//        std::vector<int32_t> fileContents;
//        for (const auto& packet : packets) {
//            fileContents.insert(fileContents.end(), packet.begin() + HEADERSIZE, packet.end());
//        }
//        return fileContents;
//    }
//
//    void MyProtocol::numberToBigEndian(int32_t number, std::vector<int32_t>& packet) {
//        packet[0] = (number >> 24) & 0xff;
//        packet[1] = (number >> 16) & 0xff;
//        packet[2] = (number >> 8) & 0xff;
//        packet[3] = number & 0xff;
//    }
//
//    int32_t MyProtocol::bigEndianToNumber(const std::vector<int32_t>& packet) {
//        return (packet[0] << 24) | (packet[1] << 16) | (packet[2] << 8) | packet[3];;
//    }
//
//    MyProtocol::MyProtocol() {
//        this->networkLayer = NULL;
//    }
//
//    MyProtocol::~MyProtocol() {
//    }
//
//    /**
//     * This is called by the framework when the server signals the simulation is done.
//     * This is mostly usefull for stopping the sender side when the simulation finishes.
//     * You may also set stop to true yourself if you want.
//     */
//    void MyProtocol::setStop(){
//        this->stop = true;
//    }
//
//    void MyProtocol::setupHandhake(int32_t numberOfPackets) {
//        std::vector<int32_t> handshakePacket = std::vector<int32_t>(HEADERSIZE);
//        std::vector<int32_t> returnHandshakePacket = std::vector<int32_t>(HEADERSIZE);
//        numberToBigEndian(numberOfPackets, handshakePacket);
//        auto waitUntilRetransmit = std::chrono::milliseconds(timeout_for_sending_in_ms);
//
//        bool finished { false };
//        while (!finished) {
//            networkLayer->sendPacket(handshakePacket);
//            bool retransmit { false };
//            auto startTime = std::chrono::system_clock::now();
//            while (!networkLayer->receivePacket(&returnHandshakePacket)) {
//                auto currentTime = std::chrono::system_clock::now();
//                if (startTime > currentTime + waitUntilRetransmit) {
//                    retransmit = true;
//                    break;
//                }
//                std::this_thread::sleep_for(std::chrono::milliseconds(10));
//            }
//
//            if (retransmit) {
//                std::cout << "Retransmitting handshake" << std::endl;
//                continue;
//            }
//
//            int32_t handshakeResponse { bigEndianToNumber(returnHandshakePacket) };
//
//            if (handshakeResponse == numberOfPackets) {
//                finished = true;
//            }
//        }
//        std::cout << "Handshake complete" << std::endl;
//
//        //std::this_thread::sleep_for(std::chrono::milliseconds(1000));
//    }
//
//    /*
//        1. Separate the data into packets and store them in a vector of vectors
//     */
//    void MyProtocol::sender() {
//        std::cout << "Sending..." << std::endl;
//
//        std::vector<int32_t> fileContents = framework::getFileContents(fileID);
//        std::ostringstream ss;
//        ss << fileContents.size();
//        std::cout << "File length: " << ss.str() << std::endl;
//
//        int32_t numberOfPackets = calculateNumberOfPackets(fileContents);
//        std::cout << "Number of packets: " << numberOfPackets << std::endl;
//
//        // setup a handshake between the sender and receiver by sending the number of packets and waiting for a confirmation to start sending
//        setupHandhake(numberOfPackets);
//
//        std::vector<std::vector<int32_t>> packetsVector(numberOfPackets);
//        std::vector<bool> acknowledgedPackets(numberOfPackets);
//
//        populatePacket(packetsVector, fileContents);
//
//        int32_t lastAcknowledgedPacket = 0;
//        int32_t nextPacketNumberToSend = 0;
//        bool inTransmission = true;
//        // The time waiting for acknowlegement from the receiver
//        auto timeDuration = std::chrono::milliseconds(timeout_for_sending_in_ms);
//
//        int consecutiveTimeouts = 0;
//        const int MAX_CONSECUTIVE_TIMEOUTS = 10;
//
//
//        while (inTransmission) {
//            networkLayer->sendPacket(packetsVector[nextPacketNumberToSend]);
//            std::cout << "Sent one packet with header = " << nextPacketNumberToSend + 1 << std::endl;
//
//            auto startTime = std::chrono::system_clock::now();
//
//            std::vector<int32_t> acknowledgedPacket;
//            if (!waitForAcknowledgement(acknowledgedPacket, startTime, timeDuration)) {
//                consecutiveTimeouts++;
//                if (consecutiveTimeouts >= MAX_CONSECUTIVE_TIMEOUTS) {
//                    std::cout << "Connection appears to be dead, stopping transmission" << std::endl;
//                    break;
//                }
//                std::cout << "Timeout exceeded\nRetransmitting unacknowledged packet\n";
//                continue;
//            }
//
//            // Reset timeout counter when we get an acknowledgment
//            consecutiveTimeouts = 0;
//
//
//            lastAcknowledgedPacket = bigEndianToNumber(acknowledgedPacket);
//            std::cout << "Last acknowledged packet " << lastAcknowledgedPacket << std::endl;
//            if (lastAcknowledgedPacket + 1 == nextPacketNumberToSend) {
//                std::cout << "All packets acknowledged\nFile sent completely" << std::endl;
//                break;
//            }
//            acknowledgedPackets[lastAcknowledgedPacket - 1] = true;
//
//            inTransmission = !findNextUnacknowledgedPacket(acknowledgedPackets, nextPacketNumberToSend);
//        }
//
//        // framework::SetTimeout(1000, this, 28);
//    }
//
//    void MyProtocol::handleHandshake(int32_t& numberOfPackets) {
//        bool handshakeFinished { false };
//
//        while (!handshakeFinished) {
//            std::vector<int32_t> handshakeReturn = std::vector<int32_t>(HEADERSIZE);
//            while (!networkLayer->receivePacket(&handshakeReturn)) {
//                std::this_thread::sleep_for(std::chrono::milliseconds(10));
//            }
//
//            numberOfPackets = bigEndianToNumber(handshakeReturn);
//
//            networkLayer->sendPacket(handshakeReturn);
//
//            // If too much time elapsed then we assume that the session started sending
//            //            auto startTime = std::chrono::system_clock::now();
//            //            auto waitTime = std::chrono::milliseconds(2000);
//            //            while (!networkLayer->receivePacket(&handshakeReturn)) {
//            //                auto currentTime = std::chrono::system_clock::now();
//            //                if (startTime > currentTime + waitTime) {
//            //                    handshakeFinished = true;
//            //                    break;
//            //                }
//            //                std::this_thread::sleep_for(std::chrono::milliseconds(10));
//            //            }
//            handshakeFinished = true;
//        }
//    }
//
//    std::vector<int32_t> MyProtocol::receiver() {
//        std::cout << "Receiving..." << std::endl;
//
//        int32_t numberOfPackets {};  // for testing
//
//        handleHandshake(numberOfPackets);
//
//        std::vector<std::vector<int32_t>> packets(numberOfPackets);
//
//        bool stop = false;
//        while (!stop) {
//            std::vector<int32_t> packet;
//
//            if (networkLayer->receivePacket(&packet)) {
//                int32_t packetNumber { bigEndianToNumber(packet) };
//
//                std::cout << "Received packet, length=" << packet.size()
//                         << "  first byte=" << packetNumber << std::endl;
//
//                packets[packetNumber - 1] = packet;
//                // sendAcknowledgement(packetNumber); // - only for when the header is 1 byte
//                std::vector<int32_t> acknowledgedPacket(HEADERSIZE);  // HEADERSIZE is 4 bytes
//                numberToBigEndian(packetNumber, acknowledgedPacket);
//                networkLayer->sendPacket(acknowledgedPacket);
//
//                stop = checkPacketsComplete(packets);
//
//            } else {
//                std::this_thread::sleep_for(std::chrono::milliseconds(10));
//            }
//        }
//
//        return assembleFileContents(packets);
//    }
//
//    void MyProtocol::TimeoutElapsed(int32_t tag) {
//        std::cout << "Timer expired with tag=" << tag << std::endl;
//    }
//
//    void MyProtocol::setFileID(std::string id) {
//        fileID = id;
//    }
//
//    void MyProtocol::setNetworkLayer(framework::NetworkLayer* nLayer) {
//        networkLayer = nLayer;
//    }
//
//} /* namespace my_protocol */
