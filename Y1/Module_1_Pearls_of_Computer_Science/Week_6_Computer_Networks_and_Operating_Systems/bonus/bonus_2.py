import matplotlib.pyplot as plt
import random
from math import comb

# N values from the problem description
N_RANGE = [1, 2, 5, 10, 20, 30, 40, 50, 60, 70, 80, 90, 100]
ALPHA_PROVIDED = 0  # Starting alpha in steps of 0.05 in [0, 1)
P_PROVIDED = 0.1  # Starting probability p in steps of 0.1 in [0.1, 1]

def expected_throughput(N, p, alpha):
    """Calculate the expected throughput E[T] in a wireless network with N computers."""
    term1 = N * p * (1 - p) ** (N - 1) * (1 - alpha) * 100

    if N > 1:
        term2 = (N * (N - 1) / 2) * p ** 2 * (1 - p) ** (N - 2) * (1 - alpha) * 200 * alpha
    else:
        term2 = 0  # No collisions possible if N = 1

    return term1 + term2

def compute_best_alpha_p(N, start_prob, start_alpha):
    alpha_prob_pair = (start_alpha, start_prob)
    pair_throughput = expected_throughput(N, start_prob, start_alpha)
    best_p = start_prob
    best_alpha = start_alpha
    
    for p in [x * 0.1 for x in range(1, 11)]:
        for a in [x * 0.05 for x in range(0, 20)]:
            exp_throughput = expected_throughput(N, p, a)
            if exp_throughput > pair_throughput:
                pair_throughput = exp_throughput
                alpha_prob_pair = (a, p)
    
    return (alpha_prob_pair, pair_throughput)

def get_winning_pairs_per_N(N_RANGE):
    pairs = []
    for N in N_RANGE:
        pairs.append((N, compute_best_alpha_p(N, P_PROVIDED, ALPHA_PROVIDED)))
    return pairs

# Get the best (alpha, p) and throughput pairs for each N
winning_pairs = get_winning_pairs_per_N(N_RANGE)

# Extract results for plotting
N_values = [pair[0] for pair in winning_pairs]
throughputs = [pair[1][1] for pair in winning_pairs]
alpha_values = [pair[1][0][0] for pair in winning_pairs]
p_values = [pair[1][0][1] for pair in winning_pairs]

# Plotting throughput vs N
plt.figure(figsize=(10, 6))
plt.plot(N_values, throughputs, marker='o', color='b', label="Throughput")
plt.xlabel("Number of Computers (N)")
plt.ylabel("Throughput")
plt.title("Throughput vs N")
plt.grid(True)
plt.legend()
plt.show()

# Plotting alpha and p values vs N
plt.figure(figsize=(10, 6))
plt.plot(N_values, alpha_values, marker='x', color='r', label="Alpha (α)")
plt.plot(N_values, p_values, marker='o', color='g', label="Probability (p)")
plt.xlabel("Number of Computers (N)")
plt.ylabel("Chosen Alpha/Probability")
plt.title("Chosen Alpha (α) and Probability (p) vs N")
plt.grid(True)
plt.legend()
plt.show()

# Print the winning pairs for each N
for pair in winning_pairs:
    print(f"N = {pair[0]}, alpha = {pair[1][0][0]:.2f}, prob = {pair[1][0][1]:.2f}, throughput = {pair[1][1]:.2f}")


def get_av_waiting_time(n_cmp, prob, n_pk=500):
    waiting_times = []  # List to hold waiting times for each packet
    queue = []  # Queue for packets waiting to be transmitted

    for _ in range(n_pk):
        # Determine if each computer sends a packet
        arrivals = [random.random() < prob for _ in range(n_cmp)]
        
        # Count how many packets arrive
        num_arrivals = sum(arrivals)

        if num_arrivals > 0:
            # If there are arrivals, add them to the queue
            for _ in range(num_arrivals):
                queue.append(0)  # 0 waiting time initially

        # Process the queue: transmit one packet if available
        if queue:
            # Transmit the first packet in the queue
            waiting_times.append(queue.pop(0))
            # Increment waiting time for the remaining packets in the queue
            queue = [wt + 1 for wt in queue]  # Increment waiting time for each packet in the queue

    # Calculate average waiting time
    avg_waiting_time = sum(waiting_times) / len(waiting_times) if waiting_times else 0
    return avg_waiting_time

def run_simulations():
    #num_computers_range = N_RANGE # Simulate from the numbers of computers from the beginning
    #num_computers_range = range(200) # Simulate in range of wanted - for test - it is exponentially increasing in computation requirements
    num_computers_range = range(1000) # Simulate in range of maximum of 10 computers to require a reasonable amount of time for waiting
    transmission_probability = 0.1
    avg_waiting_times = []

    for num_computers in num_computers_range:
        avg_waiting_time = get_av_waiting_time(num_computers, transmission_probability)
        avg_waiting_times.append(avg_waiting_time)

    # Plotting the results
    plt.figure(figsize=(30, 10))
    plt.plot(num_computers_range, avg_waiting_times, marker='o', color='b', label='Avg Waiting Time')
    plt.xlabel('Number of Computers')
    plt.ylabel('Average Waiting Time (timeslots)')
    plt.title('Average Waiting Time vs Number of Computers')
    plt.grid(True)
    plt.legend()
    plt.xticks(num_computers_range)
    plt.show()

run_simulations()
