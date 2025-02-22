/**
 * MyProtocol.cpp
 *
 *   Version: 2016-02-11
 *    Author: Jaco ter Braak & Frans van Dijk, University of Twente.
 * Copyright: University of Twente, 2015-2025
 *
 **************************************************************************
 *                          = Copyright notice =                          *
 *                                                                        *
 *            This file may  ONLY  be distributed UNMODIFIED              *
 * In particular, a correct solution to the challenge must  NOT be posted *
 * in public places, to preserve the learning effect for future students. *
 **************************************************************************
 */

#include "MyProtocol.h"

#include <algorithm>
#include <chrono>
#include <thread>

namespace my_protocol {

    constexpr int64_t timeout_for_sending_in_ms { 600 };
    constexpr int32_t WINDOW_SIZE = 10;

    int32_t MyProtocol::calculateNumberOfPackets(const std::vector<int32_t>& fileContents) {
        return (fileContents.size() % DATASIZE) ?
               (fileContents.size() / DATASIZE + 1) :
               (fileContents.size() / DATASIZE);
    }

    void MyProtocol::populatePacket(std::vector<std::vector<int32_t>>& packetsVector, const std::vector<int32_t>& fileContents) {
        uint32_t filePointer = 0;
        int32_t packetNumber = 1;

        for (std::size_t i = 0; i < packetsVector.size(); i++) {
            uint32_t datalen = std::min(DATASIZE, (uint32_t)fileContents.size() - filePointer);
            packetsVector[i] = std::vector<int32_t>(HEADERSIZE + datalen);
            numberToBigEndian(packetNumber, packetsVector[i]);
            packetNumber++;

            for (std::size_t j = HEADERSIZE; j < HEADERSIZE + datalen; j++) {
                packetsVector[i][j] = fileContents[filePointer++];
            }
        }
    }

    bool MyProtocol::waitForAcknowledgement(std::vector<int32_t>& acknowledgedPacket,
                                       std::chrono::system_clock::time_point startTime,
                                       std::chrono::milliseconds timeDuration) {
        while (!networkLayer->receivePacket(&acknowledgedPacket)) {
            std::this_thread::sleep_for(std::chrono::milliseconds(10));
            if (std::chrono::system_clock::now() - startTime > timeDuration) {
                return false;
            }
        }
        return true;
    }

    bool MyProtocol::findNextUnacknowledgedPacket(const std::vector<bool>& acknowledgedPackets, int32_t& nextPacketToSend) {
        for (std::size_t j = 0; j < acknowledgedPackets.size(); j++) {
            if (!acknowledgedPackets[j]) {
                nextPacketToSend = j;
                return false;
            }
        }
        return true;
    }

    void MyProtocol::sendAcknowledgement(int32_t packetNumber) {
        std::vector<int32_t> acknowledgedPacket(1);
        acknowledgedPacket[0] = packetNumber;
        networkLayer->sendPacket(acknowledgedPacket);
    }

    bool MyProtocol::checkPacketsComplete(const std::vector<std::vector<int32_t>>& packets) {
        for (const auto& packet : packets) {
            if (packet.size() == 0) return false;
        }
        return true;
    }

    std::vector<int32_t> MyProtocol::assembleFileContents(const std::vector<std::vector<int32_t>>& packets) {
        std::vector<int32_t> fileContents;
        for (const auto& packet : packets) {
            fileContents.insert(fileContents.end(), packet.begin() + HEADERSIZE, packet.end());
        }
        return fileContents;
    }

    void MyProtocol::numberToBigEndian(int32_t number, std::vector<int32_t>& packet) {
        packet[0] = (number >> 24) & 0xff;
        packet[1] = (number >> 16) & 0xff;
        packet[2] = (number >> 8) & 0xff;
        packet[3] = number & 0xff;
    }

    int32_t MyProtocol::bigEndianToNumber(const std::vector<int32_t>& packet) {
        return (packet[0] << 24) | (packet[1] << 16) | (packet[2] << 8) | packet[3];;
    }

    MyProtocol::MyProtocol() {
        this->networkLayer = NULL;
    }

    MyProtocol::~MyProtocol() {
    }

    /**
     * This is called by the framework when the server signals the simulation is done.
     * This is mostly usefull for stopping the sender side when the simulation finishes.
     * You may also set stop to true yourself if you want.
     */
    void MyProtocol::setStop(){
        this->stop = true;
    }

    void MyProtocol::setupHandhake(int32_t numberOfPackets) {
        std::vector<int32_t> handshakePacket = std::vector<int32_t>(HEADERSIZE);
        std::vector<int32_t> returnHandshakePacket = std::vector<int32_t>(HEADERSIZE);
        numberToBigEndian(numberOfPackets, handshakePacket);
        auto waitUntilRetransmit = std::chrono::milliseconds(timeout_for_sending_in_ms);

        bool finished { false };
        while (!finished) {
            networkLayer->sendPacket(handshakePacket);
            bool retransmit { false };
            auto startTime = std::chrono::system_clock::now();
            while (!networkLayer->receivePacket(&returnHandshakePacket)) {
                auto currentTime = std::chrono::system_clock::now();
                if (startTime > currentTime + waitUntilRetransmit) {
                    retransmit = true;
                    break;
                }
                std::this_thread::sleep_for(std::chrono::milliseconds(10));
            }

            if (retransmit) {
                std::cout << "Retransmitting handshake" << std::endl;
                continue;
            }

            int32_t handshakeResponse { bigEndianToNumber(returnHandshakePacket) };

            if (handshakeResponse == numberOfPackets) {
                finished = true;
            }
        }
        std::cout << "Handshake complete" << std::endl;

        //std::this_thread::sleep_for(std::chrono::milliseconds(1000));
    }

      bool MyProtocol::sendWindow(const std::vector<std::vector<int32_t>>& packetsVector,
                               const std::vector<bool>& acknowledgedPackets,
                               int32_t windowStart, int32_t windowEnd) {
        bool packetsSent = false;
        for (int32_t i = windowStart; i < windowEnd; i++) {
            if (!acknowledgedPackets[i]) {
                networkLayer->sendPacket(packetsVector[i]);
                std::cout << "Sent packet " << i + 1 << " in window ["
                         << windowStart + 1 << "," << windowEnd << "]" << std::endl;
                packetsSent = true;
            }
        }
        return packetsSent;
    }

    bool MyProtocol::processAcknowledgement(std::vector<bool>& acknowledgedPackets,
                                          int32_t& windowStart,
                                          int32_t numberOfPackets) {
        std::vector<int32_t> ack;
        if (!networkLayer->receivePacket(&ack)) {
            return false;
        }

        int32_t ackedPacket = bigEndianToNumber(ack) - 1;  // Convert to 0-based index
        if (ackedPacket >= 0 && ackedPacket < numberOfPackets) {
            acknowledgedPackets[ackedPacket] = true;

            // Slide window if possible
            while (windowStart < numberOfPackets && acknowledgedPackets[windowStart]) {
                windowStart++;
            }
            return true;
        }
        return false;
    }

    void MyProtocol::sender() {
        std::cout << "Sending..." << std::endl;

        // Initial setup
        std::vector<int32_t> fileContents = framework::getFileContents(fileID);
        int32_t numberOfPackets = calculateNumberOfPackets(fileContents);
        std::cout << "Number of packets: " << numberOfPackets << std::endl;

        // Handshake
        setupHandhake(numberOfPackets);

        // Prepare packets
        std::vector<std::vector<int32_t>> packetsVector(numberOfPackets);
        std::vector<bool> acknowledgedPackets(numberOfPackets, false);
        populatePacket(packetsVector, fileContents);

        // Sliding window variables
        int32_t windowStart = 0;
        int32_t windowEnd = std::min(windowStart + WINDOW_SIZE, numberOfPackets);
        int32_t consecutiveTimeouts = 0;
        const int32_t MAX_TIMEOUTS = 10;

        while (windowStart < numberOfPackets) {
            // Send all unacknowledged packets in window
            bool sentPackets = sendWindow(packetsVector, acknowledgedPackets, windowStart, windowEnd);

            // Wait for acknowledgements with timeout
            auto startTime = std::chrono::system_clock::now();
            bool ackReceived = false;

            while (std::chrono::system_clock::now() - startTime <
                   std::chrono::milliseconds(timeout_for_sending_in_ms)) {

                if (processAcknowledgement(acknowledgedPackets, windowStart, numberOfPackets)) {
                    ackReceived = true;
                    consecutiveTimeouts = 0;
                    windowEnd = std::min(windowStart + WINDOW_SIZE, numberOfPackets);
                    break;
                }

                std::this_thread::sleep_for(std::chrono::milliseconds(10));
            }

            if (!ackReceived) {
                consecutiveTimeouts++;
                std::cout << "Timeout occurred, retransmitting window" << std::endl;

                if (consecutiveTimeouts >= MAX_TIMEOUTS) {
                    std::cout << "Maximum timeouts reached, connection appears dead" << std::endl;
                    break;
                }
            }
        }
    }

    void MyProtocol::handleHandshake(int32_t& numberOfPackets) {
        bool handshakeFinished { false };

        while (!handshakeFinished) {
            std::vector<int32_t> handshakeReturn = std::vector<int32_t>(HEADERSIZE);
            while (!networkLayer->receivePacket(&handshakeReturn)) {
                std::this_thread::sleep_for(std::chrono::milliseconds(10));
            }

            numberOfPackets = bigEndianToNumber(handshakeReturn);

            networkLayer->sendPacket(handshakeReturn);

            // If too much time elapsed then we assume that the session started sending
            //            auto startTime = std::chrono::system_clock::now();
            //            auto waitTime = std::chrono::milliseconds(2000);
            //            while (!networkLayer->receivePacket(&handshakeReturn)) {
            //                auto currentTime = std::chrono::system_clock::now();
            //                if (startTime > currentTime + waitTime) {
            //                    handshakeFinished = true;
            //                    break;
            //                }
            //                std::this_thread::sleep_for(std::chrono::milliseconds(10));
            //            }
            handshakeFinished = true;
        }
    }

    std::vector<int32_t> MyProtocol::receiver() {
        std::cout << "Receiving..." << std::endl;

        // Handshake
        int32_t numberOfPackets = 0;
        handleHandshake(numberOfPackets);

        // Setup receiving buffers
        std::vector<std::vector<int32_t>> packets(numberOfPackets);
        std::vector<bool> receivedPackets(numberOfPackets, false);
        int32_t expectedPacket = 0;

        while (expectedPacket < numberOfPackets) {
            std::vector<int32_t> packet;

            if (networkLayer->receivePacket(&packet)) {
                int32_t packetNumber = bigEndianToNumber(packet) - 1;  // Convert to 0-based

                if (packetNumber >= 0 && packetNumber < numberOfPackets) {
                    std::cout << "Received packet " << packetNumber + 1
                             << ", expecting " << expectedPacket + 1 << std::endl;

                    // Store packet
                    if (!receivedPackets[packetNumber]) {
                        packets[packetNumber] = packet;
                        receivedPackets[packetNumber] = true;
                    }

                    // Send acknowledgement
                    std::vector<int32_t> ack(HEADERSIZE);
                    numberToBigEndian(packetNumber + 1, ack);
                    networkLayer->sendPacket(ack);

                    // Advance expected packet if possible
                    while (expectedPacket < numberOfPackets &&
                           receivedPackets[expectedPacket]) {
                        expectedPacket++;
                    }
                }
            } else {
                std::this_thread::sleep_for(std::chrono::milliseconds(10));
            }
        }

        return assembleFileContents(packets);
    }

    void MyProtocol::TimeoutElapsed(int32_t tag) {
        std::cout << "Timer expired with tag=" << tag << std::endl;
    }

    void MyProtocol::setFileID(std::string id) {
        fileID = id;
    }

    void MyProtocol::setNetworkLayer(framework::NetworkLayer* nLayer) {
        networkLayer = nLayer;
    }

} /* namespace my_protocol */
