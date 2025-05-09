#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include "lpm.h"

void read_routes(const char* routes);
int read_lookup(const char* lookup, const char* output);

int main(int argc, char* argv[]) {
  init();
  read_routes("routes.txt");
  return read_lookup("lookup.txt", "expected_output.txt");
}

void read_routes(const char* routes) {
    FILE *f = fopen(routes, "r");
    if (!f) {
        std::cerr << "Routes file not found! Please verify that you have your files in the correct place." << std::endl;
        std::cerr << "Missing file: " << routes << std::endl;
        exit(EXIT_FAILURE);
    }
    char s[80];

    while (fgets(s, 80, f)) {
        unsigned int a, b, c, d, ip;
        int pl, pn;

        sscanf(s, "%i.%i.%i.%i/%i %i", &a, &b, &c, &d, &pl, &pn);
        ip = (a << 24) | (b << 16) | (c << 8) | d;

        add_route(ip, pl, pn);
    }
    finalize_routes();

    fclose(f);
}

int read_lookup(const char* lookup, const char* output) {
    FILE *flookup = fopen(lookup, "r");
    FILE *foutput = fopen(output, "r");
    if (!flookup) {
        std::cerr << "Routes file not found! Please verify that you have your files in the correct place." << std::endl;
        std::cerr << "Missing file: " << lookup << std::endl;
        exit(EXIT_FAILURE);
    }
    if (!foutput) {
        std::cerr << "Routes file not found! Please verify that you have your files in the correct place." << std::endl;
        std::cerr << "Missing file: " << output << std::endl;
        exit(EXIT_FAILURE);
    }
    char slookup[80];
    char soutput[80];

    while (fgets(slookup, 80, flookup)) {
        if (fgets(soutput, 80, foutput)) {
            unsigned int a, b, c, d, ip, res;
            int pn;

            sscanf(slookup, "%i.%i.%i.%i", &a, &b, &c, &d);
            sscanf(soutput, "%i", &res);
            ip = (a << 24) | (b << 16) | (c << 8) | d;

            pn = lookup_ip(ip);

            if (pn != res) {
                printf("Error in lookup: %i.%i.%i.%i, expected: %i, actual: %i\n", a, b, c, d, res, pn);
                fclose(flookup);
                fclose(foutput);
                return 1;
            }
        }
    }
    printf("All lookups done successfully!\n");

    fclose(flookup);
    fclose(foutput);

    return 0;
}
