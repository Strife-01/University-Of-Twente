/**
 * main.cpp
 *
 *   Version: 2019-03-03
 *    Author: Jaco ter Braak & Frans van Dijk, University of Twente.
 * Copyright: University of Twente, 2015-2019
 */

#include <iostream>
#include <string>
#include <sys/types.h>
#include <cstdint>

#if defined _MSC_VER || defined __MINGW32__ || defined __CYGWIN__
#include <conio.h>
#else
#include <sys/select.h>
#endif

#include "../framework/MACChallengeClient.h"
#include "MyProtocol.h"
#include "SlottedAlohaSimplified.h"

using namespace my_protocol;

// Change to your group authentication token
std::string groupToken = "14a7d382-13a0-4b53-8d76-fc14cef8c6a2";

// The protocol implementation, change below
framework::IMACProtocol *protocolImpl = new MyProtocol();
//framework::IMACProtocol *protocolImpl = new SlottedAlohaSimplified();

// Challenge server address
std::string serverAddress = "challenges.dacs.utwente.nl";

// Challenge server port
int serverPort = 8003;

// *                                                          *
// **                                                        **
// ***             DO NOT EDIT BELOW THIS LINE!             ***
// **** IF YOU HAVE QUESTIONS PLEASE DO ASK A TA FOR HELP  ****
// *****                                                  *****
// ************************************************************
// ************************************************************
int main() {
#if defined _MSC_VER || defined __MINGW32__ || defined __CYGWIN__
    // Initialize Winsock
    WSADATA wsaDataUnused;
    WSAStartup(/*version*/2, &wsaDataUnused);
#endif

    std::cout << "[FRAMEWORK] Starting client... " << std::endl;

    framework::MACChallengeClient macclient(serverAddress, serverPort, groupToken);

    macclient.setListener(protocolImpl);

    std::cout << "[FRAMEWORK] Done." << std::endl;

    std::cout << "[FRAMEWORK] Press Enter to start the simulation..." << std::endl;
    std::cout
        << "[FRAMEWORK] (Simulation will also be started automatically if another client in the group issues the start command)"
        << std::endl;


#if !defined _MSC_VER && !defined __MINGW32__ && !defined __CYGWIN__
    // listen for cin non-blocking
    struct timeval tv;
    tv.tv_sec = 0;
    tv.tv_usec = 10000;
#endif

    bool startCommand = false;
    while (!macclient.isSimulationStarted()
        && !macclient.isSimulationFinished()) {

#if !defined _MSC_VER && !defined __MINGW32__ && !defined __CYGWIN__
        fd_set read_fds;
        FD_ZERO(&read_fds);
        FD_SET(0, &read_fds);
        size_t ins = select(1, &read_fds, NULL, NULL, &tv);
        if (!startCommand && ins > 0) {
#else
        // Checks the console for a recent keystroke
        if (!startCommand && _kbhit()) {
#endif
            // Request to start simulation
            macclient.requestStart();
            startCommand = true;
        }
    }

    std::cout << "[FRAMEWORK] Simulation started!" << std::endl;

    // Wait until the simulation ends
    while (!macclient.isSimulationFinished()) {
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }

    std::cout << "[FRAMEWORK] Simulation stopped! Check your performance on the server web interface." << std::endl;

    std::cout << "[FRAMEWORK] Shutting down client... " << std::endl;
    macclient.stop();
    delete protocolImpl;
    std::cout << "[FRAMEWORK] Done." << std::endl;

#if defined _MSC_VER || defined __MINGW32__ || defined __CYGWIN__
    // De-initialize Winsock
    WSACleanup();
#endif
}
