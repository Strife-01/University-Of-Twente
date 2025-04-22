// Longest Prefix Matching

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

// Back to 20 bits to save memory
#define DIRECT_BITS 20
#define DIRECT_SIZE (1 << DIRECT_BITS)

#define MAX_TRIE_DEPTH (32 - DIRECT_BITS)

// Reduced cache size to save memory
#define LOOKUP_CACHE_SIZE 30000
#define LOOKUP_CACHE_MASK (LOOKUP_CACHE_SIZE - 1)

void ip2human(unsigned int ip);

// Simple node structure without extras
struct TrieNode {
    int8_t port;
    uint32_t left_idx;
    uint32_t right_idx;
};

// Compact cache entry
struct LookupCacheEntry {
    uint32_t ip;
    int8_t port;
    uint8_t valid;
};

// Reduced node pool size
#define NODE_POOL_SIZE 2200000
TrieNode* node_pool = NULL;
uint32_t next_node_idx = 1;

uint32_t* direct_table = NULL;

LookupCacheEntry lookup_cache[LOOKUP_CACHE_SIZE];

// Default route and handling
int default_route = -1;
bool adding_default_route = false;

// Speed-focused inline function
inline TrieNode* idx_to_node(uint32_t idx) {
    if (idx == 0) return NULL;
    return &node_pool[idx - 1];  // Use 1-indexed for NULL optimization
}

// Create node with graceful handling of exhaustion
uint32_t create_node() {
    if (next_node_idx >= NODE_POOL_SIZE) {
        if (adding_default_route) {
            // Just return 0 for default routes
            return 0;
        }
        fprintf(stderr, "Node pool exhausted\n");
        exit(1);
    }

    uint32_t idx = next_node_idx++;
    TrieNode* node = &node_pool[idx - 1];  // -1 for 0-indexed array
    node->port = -1;
    node->left_idx = 0;
    node->right_idx = 0;

    return idx;
}

void init() {
    // Allocate node pool
    node_pool = (TrieNode*)calloc(NODE_POOL_SIZE, sizeof(TrieNode));
    if (!node_pool) {
        fprintf(stderr, "Failed to allocate node pool\n");
        exit(1);
    }

    next_node_idx = 1;  // Start from 1, 0 represents NULL

    // Allocate direct table
    direct_table = (uint32_t*)calloc(DIRECT_SIZE, sizeof(uint32_t));
    if (!direct_table) {
        fprintf(stderr, "Failed to allocate direct table\n");
        free(node_pool);
        exit(1);
    }

    // Initialize lookup cache
    memset(lookup_cache, 0, sizeof(lookup_cache));

    // Reset default route
    default_route = -1;
}

// Memory-efficient default route handling
void add_default_route(int port_number) {
    default_route = port_number;

    // Set flag to avoid crashing on node pool exhaustion
    adding_default_route = true;

    // Only create nodes for entries that don't exist
    for (unsigned int i = 0; i < DIRECT_SIZE; i++) {
        if (direct_table[i] == 0) {
            uint32_t node_idx = create_node();
            if (node_idx == 0) {
                // If node pool exhausted, just continue
                continue;
            }
            direct_table[i] = node_idx;
            TrieNode* node = idx_to_node(node_idx);
            node->port = port_number;
        } else {
            TrieNode* node = idx_to_node(direct_table[i]);
            if (node->port == -1) {
                node->port = port_number;
            }
        }
    }

    adding_default_route = false;
}

void add_route(unsigned int ip, int prefix_length, int port_number) {
    // Special handling for default route (0/0)
    if (prefix_length == 0) {
        add_default_route(port_number);
        return;
    }

    // Handle direct table routes
    if (prefix_length <= DIRECT_BITS) {
        unsigned int mask = 0xFFFFFFFF << (32 - prefix_length);
        unsigned int prefix = ip & mask;
        unsigned int start = prefix >> (32 - DIRECT_BITS);
        unsigned int count = 1 << (DIRECT_BITS - prefix_length);

        for (unsigned int i = 0; i < count; i++) {
            unsigned int idx = start + i;
            if (idx < DIRECT_SIZE) {
                if (direct_table[idx] == 0) {
                    direct_table[idx] = create_node();
                }
                TrieNode* node = idx_to_node(direct_table[idx]);
                node->port = port_number;
            }
        }
        return;
    }

    // Handle longer prefixes
    unsigned int direct_index = ip >> (32 - DIRECT_BITS);
    if (direct_index < DIRECT_SIZE) {
        if (direct_table[direct_index] == 0) {
            direct_table[direct_index] = create_node();
        }

        TrieNode* node = idx_to_node(direct_table[direct_index]);

        for (int i = DIRECT_BITS; i < prefix_length && node; i++) {
            int bit = (ip >> (31 - i)) & 1;

            if (bit == 0) {
                if (node->left_idx == 0) {
                    node->left_idx = create_node();
                }
                node = idx_to_node(node->left_idx);
            } else {
                if (node->right_idx == 0) {
                    node->right_idx = create_node();
                }
                node = idx_to_node(node->right_idx);
            }
        }

        if (node) {
            node->port = port_number;
        }
    }
}

void finalize_routes() {
    // Clear the lookup cache
    memset(lookup_cache, 0, sizeof(lookup_cache));
}

// Highly optimized lookup function
int lookup_ip(unsigned int ip) {
    // Check cache first
    uint32_t cache_idx = (ip >> 10) & LOOKUP_CACHE_MASK;
    if (lookup_cache[cache_idx].valid && lookup_cache[cache_idx].ip == ip) {
        return lookup_cache[cache_idx].port;
    }

    // Direct table lookup
    unsigned int direct_index = ip >> (32 - DIRECT_BITS);
    int best_match = default_route;  // Start with default route

    if (direct_index < DIRECT_SIZE && direct_table[direct_index] != 0) {
        TrieNode* node = idx_to_node(direct_table[direct_index]);
        best_match = (node->port != -1) ? node->port : best_match;

        // Fast path for most common case - direct table leaf node
        if (node->left_idx == 0 && node->right_idx == 0) {
            // Update cache and return
            lookup_cache[cache_idx].ip = ip;
            lookup_cache[cache_idx].port = best_match;
            lookup_cache[cache_idx].valid = 1;
            return best_match;
        }

        // Need to traverse the trie
        uint32_t bits_field = ip << DIRECT_BITS;

        // Process 4 bits at a time initially (unrolled hot path)
        #define PROCESS_BIT(pos) \
            if (node->port != -1) best_match = node->port; \
            int bit##pos = (bits_field >> 31) & 1; \
            bits_field <<= 1; \
            node = idx_to_node(bit##pos ? node->right_idx : node->left_idx); \
            if (!node) goto done;

        // Unroll first 4 bits for speed
        PROCESS_BIT(0)
        PROCESS_BIT(1)
        PROCESS_BIT(2)
        PROCESS_BIT(3)

        // Process remaining bits
        for (int i = DIRECT_BITS + 4; i < 32 && node; i++) {
            if (node->port != -1) {
                best_match = node->port;
            }

            int bit = (bits_field >> 31) & 1;
            bits_field <<= 1;

            node = idx_to_node(bit ? node->right_idx : node->left_idx);
        }

        // Check last node
        if (node && node->port != -1) {
            best_match = node->port;
        }
    }

done:
    // Update cache
    lookup_cache[cache_idx].ip = ip;
    lookup_cache[cache_idx].port = best_match;
    lookup_cache[cache_idx].valid = 1;

    return best_match;
}

// Calculate memory usage
size_t get_memory_usage() {
    size_t node_pool_mem = NODE_POOL_SIZE * sizeof(TrieNode);
    size_t direct_table_mem = DIRECT_SIZE * sizeof(uint32_t);
    size_t cache_mem = sizeof(lookup_cache);
    size_t total = node_pool_mem + direct_table_mem + cache_mem;

    printf("Memory usage breakdown:\n");
    printf("  Node pool: %.2f MB (%.2f%%)\n",
           node_pool_mem / (1024.0 * 1024.0),
           (node_pool_mem * 100.0) / total);
    printf("  Direct table: %.2f MB (%.2f%%)\n",
           direct_table_mem / (1024.0 * 1024.0),
           (direct_table_mem * 100.0) / total);
    printf("  Lookup cache: %.2f MB (%.2f%%)\n",
           cache_mem / (1024.0 * 1024.0),
           (cache_mem * 100.0) / total);
    printf("  Total: %.2f MB\n", total / (1024.0 * 1024.0));

    return total;
}

void ip2human(unsigned int ip) {
     unsigned int a, b, c, d;

     a = (ip >> 24) & 0xff;
     b = (ip >> 16) & 0xff;
     c = (ip >>  8) & 0xff;
     d =  ip        & 0xff;

     printf("%i.%i.%i.%i\n", a, b, c, d);
}
