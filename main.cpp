#include <bits/stdc++.h>
#include "parser.h"

#define all(v) v.begin(), v.end()

using namespace std;

/**
 * Global Constants
 */
const string TRACE = "trace";
const string SHOW_STATISTICS = "stats";
const string ALGORITHMS[9] = {"", "FCFS", "RR-", "SPN", "SRT", "HRRN", "FB-1", "FB-2i", "AGING"};

/**
 * Sorting Predicates
 */
bool sortByServiceTime(const tuple<string, int, int> &a, const tuple<string, int, int> &b) {
    return (get<2>(a) < get<2>(b));
}

bool sortByArrivalTime(const tuple<string, int, int> &a, const tuple<string, int, int> &b) {
    return (get<1>(a) < get<1>(b));
}

bool descendinglyByResponseRatio(const tuple<string, double, int> &a, const tuple<string, double, int> &b) {
    return get<1>(a) > get<1>(b);
}

bool byPriorityLevel(const tuple<int, int, int> &a, const tuple<int, int, int> &b) {
    if (get<0>(a) == get<0>(b))
        return get<2>(a) > get<2>(b);
    return get<0>(a) > get<0>(b);
}

/**
 * Helper Functions for Process Properties
 */
string getProcessName(const tuple<string, int, int> &a) {
    return get<0>(a);
}

int getArrivalTime(const tuple<string, int, int> &a) {
    return get<1>(a);
}

int getServiceTime(const tuple<string, int, int> &a) {
    return get<2>(a);
}

int getPriorityLevel(const tuple<string, int, int> &a) {
    return get<2>(a);
}

/**
 * Utility Functions
 */
void clearTimeline() {
    for (int i = 0; i < last_instant; i++)
        for (int j = 0; j < process_count; j++)
            timeline[i][j] = ' ';
}

double calculateResponseRatio(int waitTime, int serviceTime) {
    return (waitTime + serviceTime) * 1.0 / serviceTime;
}

void fillInWaitTime() {
    for (int i = 0; i < process_count; i++) {
        int arrivalTime = getArrivalTime(processes[i]);
        for (int k = arrivalTime; k < finishTime[i]; k++) {
            if (timeline[k][i] != '*')
                timeline[k][i] = '.';
        }
    }
}

/**
 * Scheduling Algorithms Implementation
 */

/**
 * First Come First Serve Algorithm
 * Processes are executed in the order they arrive
 */
void firstComeFirstServe() {
    int time = getArrivalTime(processes[0]);
    for (int i = 0; i < process_count; i++) {
        int processIndex = i;
        int arrivalTime = getArrivalTime(processes[i]);
        int serviceTime = getServiceTime(processes[i]);

        finishTime[processIndex] = time + serviceTime;
        turnAroundTime[processIndex] = finishTime[processIndex] - arrivalTime;
        normTurn[processIndex] = turnAroundTime[processIndex] * 1.0 / serviceTime;

        for (int j = time; j < finishTime[processIndex]; j++)
            timeline[j][processIndex] = '*';
        for (int j = arrivalTime; j < time; j++)
            timeline[j][processIndex] = '.';
            
        time += serviceTime;
    }
}

/**
 * Round Robin Algorithm
 * Processes are executed in time slices (quantum)
 * @param originalQuantum The time quantum for each process
 */
void roundRobin(int originalQuantum) {
    queue<pair<int, int>> q; // Process index, remaining service time
    int j = 0;
    
    // Add first process to queue if it arrives at time 0
    if (j < process_count && getArrivalTime(processes[j]) == 0) {
        q.push(make_pair(j, getServiceTime(processes[j])));
        j++;
    }
    
    int currentQuantum = originalQuantum;
    
    for (int time = 0; time < last_instant; time++) {
        // Process arrivals at the current time
        while (j < process_count && getArrivalTime(processes[j]) == time) {
            q.push(make_pair(j, getServiceTime(processes[j])));
            j++;
        }
        
        if (!q.empty()) {
            int processIndex = q.front().first;
            q.front().second = q.front().second - 1;
            int remainingServiceTime = q.front().second;
            int arrivalTime = getArrivalTime(processes[processIndex]);
            int serviceTime = getServiceTime(processes[processIndex]);
            currentQuantum--;
            timeline[time][processIndex] = '*';
            
            // Check for new arrivals at next time
            while (j < process_count && getArrivalTime(processes[j]) == time + 1) {
                q.push(make_pair(j, getServiceTime(processes[j])));
                j++;
            }

            // Quantum expired and process completed
            if (currentQuantum == 0 && remainingServiceTime == 0) {
                finishTime[processIndex] = time + 1;
                turnAroundTime[processIndex] = finishTime[processIndex] - arrivalTime;
                normTurn[processIndex] = turnAroundTime[processIndex] * 1.0 / serviceTime;
                currentQuantum = originalQuantum;
                q.pop();
            } 
            // Quantum expired but process not completed
            else if (currentQuantum == 0 && remainingServiceTime != 0) {
                q.pop();
                q.push(make_pair(processIndex, remainingServiceTime));
                currentQuantum = originalQuantum;
            } 
            // Process completed before quantum expires
            else if (currentQuantum != 0 && remainingServiceTime == 0) {
                finishTime[processIndex] = time + 1;
                turnAroundTime[processIndex] = finishTime[processIndex] - arrivalTime;
                normTurn[processIndex] = turnAroundTime[processIndex] * 1.0 / serviceTime;
                q.pop();
                currentQuantum = originalQuantum;
            }
        }
        
        // Check for new arrivals at the next time
        while (j < process_count && getArrivalTime(processes[j]) == time + 1) {
            q.push(make_pair(j, getServiceTime(processes[j])));
            j++;
        }
    }
    
    fillInWaitTime();
}

/**
 * Shortest Process Next Algorithm
 * Non-preemptive algorithm that selects the process with shortest service time
 */
void shortestProcessNext() {
    // Min heap: pair of service time and process index
    priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> readyQueue;
    int j = 0;
    
    for (int i = 0; i < last_instant; i++) {
        // Add newly arrived processes to the ready queue
        while (j < process_count && getArrivalTime(processes[j]) <= i) {
            readyQueue.push(make_pair(getServiceTime(processes[j]), j));
            j++;
        }
        
        if (!readyQueue.empty()) {
            int processIndex = readyQueue.top().second;
            int arrivalTime = getArrivalTime(processes[processIndex]);
            int serviceTime = getServiceTime(processes[processIndex]);
            readyQueue.pop();

            // Mark waiting time
            for (int temp = arrivalTime; temp < i; temp++)
                timeline[temp][processIndex] = '.';

            // Mark execution time
            for (int temp = i; temp < i + serviceTime; temp++)
                timeline[temp][processIndex] = '*';

            finishTime[processIndex] = i + serviceTime;
            turnAroundTime[processIndex] = finishTime[processIndex] - arrivalTime;
            normTurn[processIndex] = turnAroundTime[processIndex] * 1.0 / serviceTime;
            
            // Skip to the end of this process execution
            i = i + serviceTime - 1;
        }
    }
}

/**
 * Shortest Remaining Time Algorithm
 * Preemptive version of SPN that selects process with shortest remaining time
 */
void shortestRemainingTime() {
    // Min heap: pair of remaining time and process index
    priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> readyQueue;
    int j = 0;
    
    for (int i = 0; i < last_instant; i++) {
        // Add newly arrived processes to the ready queue
        while (j < process_count && getArrivalTime(processes[j]) == i) {
            readyQueue.push(make_pair(getServiceTime(processes[j]), j));
            j++;
        }
        
        if (!readyQueue.empty()) {
            int processIndex = readyQueue.top().second;
            int remainingTime = readyQueue.top().first;
            readyQueue.pop();
            
            int serviceTime = getServiceTime(processes[processIndex]);
            int arrivalTime = getArrivalTime(processes[processIndex]);
            timeline[i][processIndex] = '*';

            // Process finished
            if (remainingTime == 1) {
                finishTime[processIndex] = i + 1;
                turnAroundTime[processIndex] = finishTime[processIndex] - arrivalTime;
                normTurn[processIndex] = turnAroundTime[processIndex] * 1.0 / serviceTime;
            } else {
                // Re-add process with decremented remaining time
                readyQueue.push(make_pair(remainingTime - 1, processIndex));
            }
        }
    }
    
    fillInWaitTime();
}

/**
 * Highest Response Ratio Next Algorithm
 * Non-preemptive algorithm that selects process with highest response ratio
 */
void highestResponseRatioNext() {
    // Vector of (process_name, response_ratio, time_in_service)
    vector<tuple<string, double, int>> readyProcesses;
    int j = 0;
    
    for (int current_instant = 0; current_instant < last_instant; current_instant++) {
        // Add newly arrived processes to the ready queue
        while (j < process_count && getArrivalTime(processes[j]) <= current_instant) {
            readyProcesses.push_back(make_tuple(getProcessName(processes[j]), 1.0, 0));
            j++;
        }
        
        // Calculate response ratio for every process
        for (auto &proc : readyProcesses) {
            string process_name = get<0>(proc);
            int process_index = processToIndex[process_name];
            int wait_time = current_instant - getArrivalTime(processes[process_index]);
            int service_time = getServiceTime(processes[process_index]);
            get<1>(proc) = calculateResponseRatio(wait_time, service_time);
        }

        // Sort by highest response ratio
        sort(all(readyProcesses), descendinglyByResponseRatio);

        if (!readyProcesses.empty()) {
            int process_index = processToIndex[get<0>(readyProcesses[0])];
            
            // Execute process until completion
            while (current_instant < last_instant && 
                   get<2>(readyProcesses[0]) != getServiceTime(processes[process_index])) {
                timeline[current_instant][process_index] = '*';
                current_instant++;
                get<2>(readyProcesses[0])++;
            }
            
            current_instant--;
            readyProcesses.erase(readyProcesses.begin());
            
            finishTime[process_index] = current_instant + 1;
            turnAroundTime[process_index] = finishTime[process_index] - getArrivalTime(processes[process_index]);
            normTurn[process_index] = turnAroundTime[process_index] * 1.0 / getServiceTime(processes[process_index]);
        }
    }
    
    fillInWaitTime();
}

/**
 * Feedback Queue with Quantum 1 Algorithm
 * Multilevel queue with aging mechanism
 */
void feedbackQ1() {
    // Min heap: pair of priority level and process index
    priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> readyQueue;
    
    // Map from process index to remaining service time
    unordered_map<int, int> remainingServiceTime;
    int j = 0;
    
    // Add first process if it arrives at time 0
    if (j < process_count && getArrivalTime(processes[0]) == 0) {
        readyQueue.push(make_pair(0, j));
        remainingServiceTime[j] = getServiceTime(processes[j]);
        j++;
    }
    
    for (int time = 0; time < last_instant; time++) {
        // Process arrivals for the next time unit
        while (j < process_count && getArrivalTime(processes[j]) == time + 1) {
            readyQueue.push(make_pair(0, j));
            remainingServiceTime[j] = getServiceTime(processes[j]);
            j++;
        }
        
        if (!readyQueue.empty()) {
            int priorityLevel = readyQueue.top().first;
            int processIndex = readyQueue.top().second;
            int arrivalTime = getArrivalTime(processes[processIndex]);
            int serviceTime = getServiceTime(processes[processIndex]);
            readyQueue.pop();
            
            remainingServiceTime[processIndex]--;
            timeline[time][processIndex] = '*';
            
            // Process completed
            if (remainingServiceTime[processIndex] == 0) {
                finishTime[processIndex] = time + 1;
                turnAroundTime[processIndex] = finishTime[processIndex] - arrivalTime;
                normTurn[processIndex] = turnAroundTime[processIndex] * 1.0 / serviceTime;
            } else {
                // Requeue with increased priority level if other processes are waiting
                if (readyQueue.size() >= 1) {
                    readyQueue.push(make_pair(priorityLevel + 1, processIndex));
                } else {
                    readyQueue.push(make_pair(priorityLevel, processIndex));
                }
            }
        }
        
        // Check for new arrivals
        while (j < process_count && getArrivalTime(processes[j]) == time + 1) {
            readyQueue.push(make_pair(0, j));
            remainingServiceTime[j] = getServiceTime(processes[j]);
            j++;
        }
    }
    
    fillInWaitTime();
}

/**
 * Feedback Queue with 2^i Quantum Algorithm
 * Multilevel queue with exponentially increasing quantum
 */
void feedbackQ2i() {
    // Min heap: pair of priority level and process index
    priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> readyQueue;
    
    // Map from process index to remaining service time
    unordered_map<int, int> remainingServiceTime;
    int j = 0;
    
    // Add first process if it arrives at time 0
    if (j < process_count && getArrivalTime(processes[0]) == 0) {
        readyQueue.push(make_pair(0, j));
        remainingServiceTime[j] = getServiceTime(processes[j]);
        j++;
    }
    
    for (int time = 0; time < last_instant; time++) {
        if (!readyQueue.empty()) {
            int priorityLevel = readyQueue.top().first;
            int processIndex = readyQueue.top().second;
            int arrivalTime = getArrivalTime(processes[processIndex]);
            int serviceTime = getServiceTime(processes[processIndex]);
            readyQueue.pop();
            
            // Add newly arrived processes
            while (j < process_count && getArrivalTime(processes[j]) <= time + 1) {
                readyQueue.push(make_pair(0, j));
                remainingServiceTime[j] = getServiceTime(processes[j]);
                j++;
            }

            // Calculate quantum for current priority level: 2^i
            int currentQuantum = pow(2, priorityLevel);
            int temp = time;
            
            // Execute process for quantum duration or until completion
            while (currentQuantum > 0 && remainingServiceTime[processIndex] > 0) {
                currentQuantum--;
                remainingServiceTime[processIndex]--;
                timeline[temp++][processIndex] = '*';
            }

            // Process completed
            if (remainingServiceTime[processIndex] == 0) {
                finishTime[processIndex] = temp;
                turnAroundTime[processIndex] = finishTime[processIndex] - arrivalTime;
                normTurn[processIndex] = turnAroundTime[processIndex] * 1.0 / serviceTime;
            } else {
                // Requeue with increased priority level if other processes are waiting
                if (readyQueue.size() >= 1) {
                    readyQueue.push(make_pair(priorityLevel + 1, processIndex));
                } else {
                    readyQueue.push(make_pair(priorityLevel, processIndex));
                }
            }
            
            // Skip to the end of this time slice
            time = temp - 1;
        }
        
        // Check for new arrivals
        while (j < process_count && getArrivalTime(processes[j]) <= time + 1) {
            readyQueue.push(make_pair(0, j));
            remainingServiceTime[j] = getServiceTime(processes[j]);
            j++;
        }
    }
    
    fillInWaitTime();
}

/**
 * Aging Algorithm
 * Priority-based scheduling with dynamic priority adjustment
 * @param originalQuantum The time quantum for each process
 */
void aging(int originalQuantum) {
    // Vector of (priority_level, process_index, total_waiting_time)
    vector<tuple<int, int, int>> processQueue;
    int j = 0;
    int currentProcess = -1;
    
    for (int time = 0; time < last_instant; time++) {
        // Add newly arrived processes
        while (j < process_count && getArrivalTime(processes[j]) <= time) {
            processQueue.push_back(make_tuple(getPriorityLevel(processes[j]), j, 0));
            j++;
        }

        // Update priorities and waiting times
        for (auto &proc : processQueue) {
            if (get<1>(proc) == currentProcess) {
                // Reset waiting time and priority for the currently running process
                get<2>(proc) = 0;
                get<0>(proc) = getPriorityLevel(processes[currentProcess]);
            } else {
                // Increase priority and waiting time for waiting processes
                get<0>(proc)++;
                get<2>(proc)++;
            }
        }
        
        // Sort by priority level
        sort(processQueue.begin(), processQueue.end(), byPriorityLevel);
        
        if (!processQueue.empty()) {
            currentProcess = get<1>(processQueue[0]);
            int currentQuantum = originalQuantum;
            
            // Execute for quantum duration
            while (currentQuantum > 0 && time < last_instant) {
                timeline[time][currentProcess] = '*';
                time++;
                currentQuantum--;
            }
            
            time--;
        }
    }
    
    fillInWaitTime();
}

/**
 * Output Functions
 */
void printAlgorithm(int algorithm_index) {
    int algorithm_id = algorithms[algorithm_index].first - '0';
    if (algorithm_id == 2)
        cout << ALGORITHMS[algorithm_id] << algorithms[algorithm_index].second << endl;
    else
        cout << ALGORITHMS[algorithm_id] << endl;
}

void printProcesses() {
    cout << "Process    ";
    for (int i = 0; i < process_count; i++)
        cout << "|  " << getProcessName(processes[i]) << "  ";
    cout << "|\n";
}

void printArrivalTime() {
    cout << "Arrival    ";
    for (int i = 0; i < process_count; i++)
        printf("|%3d  ", getArrivalTime(processes[i]));
    cout << "|\n";
}

void printServiceTime() {
    cout << "Service    |";
    for (int i = 0; i < process_count; i++)
        printf("%3d  |", getServiceTime(processes[i]));
    cout << " Mean|\n";
}

void printFinishTime() {
    cout << "Finish     ";
    for (int i = 0; i < process_count; i++)
        printf("|%3d  ", finishTime[i]);
    cout << "|-----|\n";
}

void printTurnAroundTime() {
    cout << "Turnaround |";
    int sum = 0;
    for (int i = 0; i < process_count; i++) {
        printf("%3d  |", turnAroundTime[i]);
        sum += turnAroundTime[i];
    }
    
    double mean = 1.0 * sum / turnAroundTime.size();
    if (mean >= 10)
        printf("%2.2f|\n", mean);
    else
        printf(" %2.2f|\n", mean);
}

void printNormTurn() {
    cout << "NormTurn   |";
    float sum = 0;
    for (int i = 0; i < process_count; i++) {
        if (normTurn[i] >= 10)
            printf("%2.2f|", normTurn[i]);
        else
            printf(" %2.2f|", normTurn[i]);
        
        sum += normTurn[i];
    }

    double mean = 1.0 * sum / normTurn.size();
    if (mean >= 10)
        printf("%2.2f|\n", mean);
    else
        printf(" %2.2f|\n", mean);
}

void printStats(int algorithm_index) {
    printAlgorithm(algorithm_index);
    printProcesses();
    printArrivalTime();
    printServiceTime();
    printFinishTime();
    printTurnAroundTime();
    printNormTurn();
}

void printTimeline(int algorithm_index) {
    // Print time indices
    for (int i = 0; i <= last_instant; i++)
        cout << i % 10 << " ";
    cout << "\n";
    
    cout << "------------------------------------------------\n";
    
    // Print timeline for each process
    for (int i = 0; i < process_count; i++) {
        cout << getProcessName(processes[i]) << "     |";
        for (int j = 0; j < last_instant; j++) {
            cout << timeline[j][i] << "|";
        }
        cout << " \n";
    }
    
    cout << "------------------------------------------------\n";
}

/**
 * Execute the specified scheduling algorithm
 * @param algorithm_id The ID of the algorithm to execute
 * @param quantum The time quantum (for RR, AGING)
 * @param operation The operation to perform (trace or stats)
 */
void executeAlgorithm(char algorithm_id, int quantum, string operation) {
    switch (algorithm_id) {
        case '1':
            if (operation == TRACE) cout << "FCFS  ";
            firstComeFirstServe();
            break;
        case '2':
            if (operation == TRACE) cout << "RR-" << quantum << "  ";
            roundRobin(quantum);
            break;
        case '3':
            if (operation == TRACE) cout << "SPN   ";
            shortestProcessNext();
            break;
        case '4':
            if (operation == TRACE) cout << "SRT   ";
            shortestRemainingTime();
            break;
        case '5':
            if (operation == TRACE) cout << "HRRN  ";
            highestResponseRatioNext();
            break;
        case '6':
            if (operation == TRACE) cout << "FB-1  ";
            feedbackQ1();
            break;
        case '7':
            if (operation == TRACE) cout << "FB-2i ";
            feedbackQ2i();
            break;
        case '8':
            if (operation == TRACE) cout << "Aging ";
            aging(quantum);
            break;
        default:
            cerr << "Unknown algorithm ID: " << algorithm_id << endl;
            break;
    }
}

/**
 * Main function - entry point of the program
 */
int main() {
    // Parse input data
    parse();
    
    // Execute each specified algorithm
    for (int idx = 0; idx < (int)algorithms.size(); idx++) {
        clearTimeline();
        executeAlgorithm(algorithms[idx].first, algorithms[idx].second, operation);
        
        if (operation == TRACE)
            printTimeline(idx);
        else if (operation == SHOW_STATISTICS)
            printStats(idx);
            
        cout << "\n";
    }
    
    return 0;
}