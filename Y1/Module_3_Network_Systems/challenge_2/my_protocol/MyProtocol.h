/**
 * MyProtocol.h
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

#ifndef MyProtocol_H_
#define MyProtocol_H_

#include "../framework/IRDTProtocol.h"
#include "../framework/NetworkLayer.h"
#include "../framework/Utils.h"
#include <cstdio>
#include <iostream>
#include <iterator>
#include <vector>

namespace my_protocol {

    class MyProtocol : public framework::IRDTProtocol {


    public:
        MyProtocol();
        ~MyProtocol();
        void sender();
        std::vector<int32_t> receiver();
        void setNetworkLayer(framework::NetworkLayer*);
        void setFileID(std::string);
        void setStop();
        void TimeoutElapsed(int32_t);

    private:
        std::string fileID;
        framework::NetworkLayer* networkLayer;
        bool stop = false;
        const uint32_t HEADERSIZE = 4;   // number of header bytes in each packet - 4 bytes the number of representing packet
        const uint32_t DATASIZE = 300;   // max. number of user data bytes in each packet

        // Helper functions for sender
        int32_t calculateNumberOfPackets(const std::vector<int32_t>& fileContents);
        void populatePacket(std::vector<std::vector<int32_t>>& packetsVector, const std::vector<int32_t>& fileContents);
        bool waitForAcknowledgement(std::vector<int32_t>& acknowledgedPacket,
                                   std::chrono::system_clock::time_point startTime,
                                   std::chrono::milliseconds timeDuration);
        bool findNextUnacknowledgedPacket(const std::vector<bool>& acknowledgedPackets, int32_t& nextPacketToSend);
        void numberToBigEndian(int32_t number, std::vector<int32_t>& packet);
        void setupHandhake(int32_t numberOfPackets);

        // Helper functions for receiver
        void sendAcknowledgement(int32_t packetNumber);
        bool checkPacketsComplete(const std::vector<std::vector<int32_t>>& packets);
        std::vector<int32_t> assembleFileContents(const std::vector<std::vector<int32_t>>& packets);
        int32_t bigEndianToNumber(const std::vector<int32_t>& packet);
        void handleHandshake(int32_t& numberOfPackets);

        // New helper functions for sliding window
        bool sendWindow(const std::vector<std::vector<int32_t>>& packetsVector,
                       const std::vector<bool>& acknowledgedPackets,
                       int32_t windowStart, int32_t windowEnd);
        bool processAcknowledgement(std::vector<bool>& acknowledgedPackets,
                                  int32_t& windowStart,
                                  int32_t numberOfPackets);
    };

} /* namespace my_protocol */

#endif /* MyProtocol_H_ */
