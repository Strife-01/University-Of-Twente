/**
 * SlottedAlohaSimplified.cpp
 *
 *   Version: 2015-02-15
 *    Author: Jaco ter Braak, University of Twente.
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

#include "SlottedAlohaSimplified.h"

namespace my_protocol {

    using std::cout;

    SlottedAlohaSimplified::SlottedAlohaSimplified() {
        unsigned int seed = std::chrono::steady_clock::now().time_since_epoch().count(); // This grabs the lower 32 bits for our seed.
        this->rnd = std::default_random_engine(seed);
    }

    SlottedAlohaSimplified::~SlottedAlohaSimplified() {
    }

    TransmissionInfo SlottedAlohaSimplified::TimeslotAvailable(
        MediumState previousMediumState, int32_t controlInformation, int localQueueLength) {
        cout << "[FRAMEWORK] previousMediumState: " << previousMediumState << '\n';
        cout << "[FRAMEWORK] controlInformation: " << controlInformation << '\n';
        cout << "[FRAMEWORK] localQueueLength: " << localQueueLength << '\n';
        cout << "\n\n";
        // No data to send, just be quiet
        if (localQueueLength == 0) {
            std::cout << "SLOT - No data to send." << std::endl;
            return TransmissionInfo{ Silent, 0 };
        }

        // Randomly transmit with 60 probability
        if (this->rnd() % 100 < 60) {
            std::cout << "SLOT - Sending data and hope for no collision." << std::endl;
            return TransmissionInfo{ Data, 1 };
        }
        else {
            std::cout << "SLOT - Not sending data to give room for others." << std::endl;
            return TransmissionInfo{ Silent, 0 };
        }

    }

} /* namespace my_protocol */
