#include "MyProtocol.h"

namespace my_protocol {

    using std::cout;

    MyProtocol::MyProtocol()
    : rnd {}
    , collision_count {}
    , max_nr_or_interrupted_sendings { FAIRNESS_INTERRUPTION_COUNTER }
    , backoff_slots {}
    , node_id { getThreadId() % NODE_ID_MOD }  // Ensure node_id is reasonably sized
    , transmission_probability { INITIAL_TX_PROBABILITY }
    , consecutive_successes { 0 }
    , consecutive_collisions { 0 }
    , network_load_estimate { 0 }
    {
        unsigned int seed = std::chrono::steady_clock::now().time_since_epoch().count();
        this->rnd = std::default_random_engine(seed);
    }

    MyProtocol::~MyProtocol() {
    }

    TransmissionInfo MyProtocol::TimeslotAvailable(
        MediumState previousMediumState, int32_t controlInformation, int localQueueLength) {

        // Debug output
        cout << "[DEBUG] State: " << previousMediumState
            << ", Collision count: " << (int)collision_count
            << ", Backoff slots: " << backoff_slots
            << ", Queue: " << localQueueLength
            << ", Tx Prob: " << transmission_probability << "%"
            << ", Control Information: " << controlInformation << '\n';

        if (localQueueLength == 0) {
            collision_count = 0;
            backoff_slots = 0;
            max_nr_or_interrupted_sendings = 0;

            // Reset success/collision counters when queue empties
            consecutive_successes = 0;
            consecutive_collisions = 0;

            return TransmissionInfo{ Silent, 0 };
        }

        if (backoff_slots > 0) {
            backoff_slots--;
            cout << "[DEBUG] In backoff, " << backoff_slots << " slots remaining\n";
            return TransmissionInfo{ Silent, 0 };
        }

        if (previousMediumState == Idle) {
            collision_count = 0;
            consecutive_collisions = 0;

            // Adaptive transmission probability based on network conditions
            if (this->rnd() % 100 < transmission_probability) {
                return TransmissionInfo{ Data, node_id };
            } else {
                return TransmissionInfo{ Silent, 0 };
            }
        }
        else if (previousMediumState == Success) {
            if (controlInformation == node_id) {
                // Our transmission was successful
                collision_count = 0;
                consecutive_collisions = 0;
                consecutive_successes++;

                // Adaptively increase transmission probability with consecutive successes
                // but cap it to avoid too aggressive behavior
                if (consecutive_successes > SUCCESS_STREAK_THRESHOLD &&
                    transmission_probability < MAX_TX_PROBABILITY) {
                    transmission_probability += TX_PROBABILITY_INCREMENT;
                    if (transmission_probability > MAX_TX_PROBABILITY) {
                        transmission_probability = MAX_TX_PROBABILITY;
                    }
                }

                // Update network load estimate - successful transmission suggests lower load
                network_load_estimate -= NETWORK_LOAD_DECREMENT;
                if (network_load_estimate < MIN_NETWORK_LOAD) {
                    network_load_estimate = MIN_NETWORK_LOAD;
                }

                if (!network_load_estimate) {
                    return TransmissionInfo{ Data, node_id };
                }

                if (max_nr_or_interrupted_sendings) {
                    max_nr_or_interrupted_sendings--;
                    return TransmissionInfo{ Data, node_id };
                }
                else {
                    max_nr_or_interrupted_sendings = FAIRNESS_INTERRUPTION_COUNTER;
                    return TransmissionInfo{ Silent, 0 };
                }
            }
            else {
                // Someone else's transmission was successful
                consecutive_successes = 0;

                // Slightly decrease transmission probability when others are transmitting
                if (transmission_probability > MIN_TX_PROBABILITY) {
                    transmission_probability -= OTHER_TX_PROBABILITY_DECREMENT;
                    if (transmission_probability < MIN_TX_PROBABILITY) {
                        transmission_probability = MIN_TX_PROBABILITY;
                    }
                }

                return TransmissionInfo{ Silent, 0 };
            }
        }
        else if (previousMediumState == Collision) {
            // Track collisions for adaptive behavior
            consecutive_collisions++;
            consecutive_successes = 0;

            // Update network load estimate - collisions suggest higher load
            network_load_estimate += NETWORK_LOAD_INCREMENT;
            if (network_load_estimate > MAX_NETWORK_LOAD) {
                network_load_estimate = MAX_NETWORK_LOAD;
            }

            // Adaptively decrease transmission probability based on collision rate
            if (consecutive_collisions > 1) {
                transmission_probability -= COLLISION_TX_PROBABILITY_DECREMENT;
                if (transmission_probability < MIN_TX_PROBABILITY) {
                    transmission_probability = MIN_TX_PROBABILITY;
                }
            }

            if (collision_count < MAX_COLLISION_COUNT) {
                collision_count++;
            }

            // Compute backoff window: 2^collision_count - 1
            // But cap at a reasonable maximum to avoid excessive delays
            uint8_t backoff_exponent = collision_count;
            if (backoff_exponent > MAX_BACKOFF_EXPONENT) {
                backoff_exponent = MAX_BACKOFF_EXPONENT;  // Cap exponent to prevent overflow
            }
            uint16_t backoff_window = (1 << backoff_exponent) - 1;

            // Ensure window is at least 1 and not too large
            if (backoff_window > MAX_BACKOFF_WINDOW) {
                backoff_window = MAX_BACKOFF_WINDOW;
            }
            if (backoff_window < 1) {
                backoff_window = 1;
            }

            // Add small perturbation using node ID without risking overflow
            uint16_t node_perturbation = static_cast<uint16_t>(node_id % NODE_PERTURBATION_MOD);
            if (backoff_window + node_perturbation <= MAX_BACKOFF_WINDOW) {
                backoff_window += node_perturbation;
            }

            // Select backoff slots, but adjust distribution based on network load
            // Higher load -> favor larger backoff values
            int r = this->rnd() % 100;
            if (network_load_estimate > HIGH_LOAD_THRESHOLD && r < HIGH_LOAD_BACKOFF_BIAS) {
                // In high load, bias toward larger backoff values
                uint16_t half_window = backoff_window / 2;
                backoff_slots = (this->rnd() % (half_window + 1)) + half_window;
            } else {
                // Normal backoff selection
                backoff_slots = this->rnd() % (backoff_window + 1);
            }

            // Ensure backoff_slots doesn't exceed MAX_BACKOFF_WINDOW
            if (backoff_slots > MAX_BACKOFF_WINDOW) {
                backoff_slots = MAX_BACKOFF_WINDOW;
            }

            cout << "[DEBUG] Collision #" << (int)collision_count
                 << ", window: 0-" << backoff_window
                 << ", chosen backoff: " << backoff_slots
                 << ", network load: " << network_load_estimate << "%\n";

            if (backoff_slots == 0) {
                // Adaptive immediate retransmission
                // In high collision scenarios, reduce chance of immediate retransmission
                if (consecutive_collisions >= CONSECUTIVE_COLLISION_THRESHOLD &&
                    (this->rnd() % 100 < IMMEDIATE_RETRANSMISSION_PENALTY)) {
                    // Force at least some backoff in high-collision scenarios
                    backoff_slots = MIN_FORCED_BACKOFF +
                                    (this->rnd() % (MAX_FORCED_BACKOFF - MIN_FORCED_BACKOFF + 1));
                    return TransmissionInfo{ Silent, 0 };
                }

                return TransmissionInfo{ Data, node_id };
            } else {
                return TransmissionInfo{ Silent, 0 };
            }
        }

        // Should never happen
        return TransmissionInfo{ NoData, node_id };
    }

    int32_t MyProtocol::getThreadId() {
        // Get native thread handle
        std::thread::id threadId = std::this_thread::get_id();

        // Convert to integer (hash-based, not guaranteed to fit in int32_t)
        std::hash<std::thread::id> hasher;
        std::size_t hashValue = hasher(threadId);

        // Cast to int32_t (may lose information)
        return static_cast<int32_t>(hashValue);
    }

} /* namespace my_protocol */