/**
 * MyProtocol.h
 *
 *   Version: 2015-02-15
 *    Author: Jaco ter Braak, University of Twente.
 * Copyright: University of Twente, 2015-2025
 *
 **************************************************************************
 *                            Copyright notice                            *
 *                                                                        *
 *            This file may  ONLY  be distributed UNMODIFIED              *
 * In particular, a correct solution to the challenge must  NOT be posted *
 * in public places, to preserve the learning effect for future students. *
 **************************************************************************
 */

#include "../framework/IMACProtocol.h"
#include <cstdint>
#include <cstdlib>
#include <chrono>
#include <random>
#include <iostream>


#ifndef PROTOCOL_MYPROTOCOL_H_
#define PROTOCOL_MYPROTOCOL_H_

#include <thread>

// Protocol configuration parameters
#define FAIRNESS_INTERRUPTION_COUNTER          5   // How many successful transmissions before yielding
#define MAX_BACKOFF_WINDOW                     64U  // Cap backoff window to prevent excessive delays
#define MAX_COLLISION_COUNT                    10   // Maximum collision count to track
#define MAX_BACKOFF_EXPONENT                   10   // Prevent exponential backoff overflow
#define INITIAL_TX_PROBABILITY                 85   // Starting transmission probability (%)
#define MAX_TX_PROBABILITY                     95   // Maximum transmission probability (%)
#define MIN_TX_PROBABILITY                     30   // Minimum transmission probability (%)
#define SUCCESS_STREAK_THRESHOLD               2    // Consecutive successes before increasing tx probability
#define TX_PROBABILITY_INCREMENT               5    // How much to increase tx probability after success streak
#define OTHER_TX_PROBABILITY_DECREMENT         5    // How much to decrease tx probability when others succeed
#define COLLISION_TX_PROBABILITY_DECREMENT     5    // How much to decrease tx probability after collision
#define NETWORK_LOAD_INCREMENT                 5    // Increment for network load estimate on collision
#define NETWORK_LOAD_DECREMENT                 5    // Decrement for network load estimate on success
#define MAX_NETWORK_LOAD                       100  // Maximum network load estimate value
#define MIN_NETWORK_LOAD                       0    // Minimum network load estimate value
#define HIGH_LOAD_THRESHOLD                    60   // Network load threshold considered "high"
#define HIGH_LOAD_BACKOFF_BIAS                 30   // Probability (%) to bias toward larger backoff values in high load
#define CONSECUTIVE_COLLISION_THRESHOLD        3    // Collisions before forcing non-zero backoff
#define IMMEDIATE_RETRANSMISSION_PENALTY       80   // Probability (%) to force backoff after multiple collisions
#define MIN_FORCED_BACKOFF                     1    // Minimum forced backoff slots
#define MAX_FORCED_BACKOFF                     3    // Maximum forced backoff slots
#define NODE_ID_MOD                            1024  // Range for node_id values
#define NODE_PERTURBATION_MOD                  3    // Modulo for node perturbation

namespace my_protocol {

    class MyProtocol : public framework::IMACProtocol {
    public:
        MyProtocol();
        ~MyProtocol();
        TransmissionInfo TimeslotAvailable(MediumState previousMediumState, int32_t controlInformation, int localQueueLength);

    private:
        int32_t getThreadId();

        std::default_random_engine rnd;
        uint8_t collision_count;
        uint8_t max_nr_or_interrupted_sendings;
        uint16_t backoff_slots;
        int32_t node_id;

        // Adaptive optimization variables
        int transmission_probability;     // Adaptive transmission probability (0-100%)
        uint8_t consecutive_successes;    // Counter for consecutive successful transmissions
        uint8_t consecutive_collisions;   // Counter for consecutive collisions
        int network_load_estimate;        // Estimate of current network load (0-100%)
    };

} /* namespace my_protocol */

#endif /* PROTOCOL_MYPROTOCOL_H_ */