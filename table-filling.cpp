#include <iostream>
#include <vector>
#include <algorithm>
#include <string>
#include <queue>
using namespace std;

class DFA {
private:
    int numStates;
    int startState;
    vector<char> alphabet;
    vector<vector<int>> transitionTable;
    vector<int> FinalStates;

public:
    DFA() : numStates(0), startState(0) {}

    DFA(int n, vector<char> alphabet, int startState,
        vector<vector<int>> transitionTable, vector<int> FinalStates)
        : numStates(n), startState(startState),
          alphabet(alphabet), transitionTable(transitionTable),
          FinalStates(FinalStates) {}

    int getNumStates() const {
        return numStates;
    }

    vector<char> getAlphabet() const {
        return alphabet;
    }

    int getStartState() const {
        return startState;
    }

    vector<int> getFinalStates() const {
        return FinalStates;
    }

    bool isFinal(int state) const {
        return find(FinalStates.begin(), FinalStates.end(), state)
               != FinalStates.end();
    }

    int getTransition(int state, int symbolIndex) const {
        return transitionTable[state][symbolIndex];
    }

    vector<vector<int>> getTransitionTable() const {
        return transitionTable;
    }

    void setNumStates(int n) {
        numStates = n;
    }

    void setStartState(int s) {
        startState = s;
    }

    void setAlphabet(const vector<char>& a) {
        alphabet = a;
    }

    void setTransition(int state, int symbolIndex, int nextState) {
        transitionTable[state][symbolIndex] = nextState;
    }

    void setTransitionTable(const vector<vector<int>>& t) {
        transitionTable = t;
    }

    void setFinalStatesList(const vector<int>& f) {
        FinalStates = f;
    }
};

class DFAvalidator {
public:
    static bool isValid(const DFA& dfa) {
        int numStates = dfa.getNumStates();
        vector<char> alphabet = dfa.getAlphabet();
        int startState = dfa.getStartState();
        vector<vector<int>> transitionTable = dfa.getTransitionTable();

        if (numStates <= 0)
            return false;

        if (alphabet.empty())
            return false;

        if (startState < 0 || startState >= numStates)
            return false;

        for (int finalState : dfa.getFinalStates()) {
            if (finalState < 0 || finalState >= numStates)
                return false;
        }

        if (transitionTable.size() != static_cast<size_t>(numStates))
            return false;

        for (const auto& row : transitionTable) {
            if (row.size() != alphabet.size())
                return false;

            for (int state : row) {
                if (state < -1 || state >= numStates)
                    return false;
            }
        }

        return true;
    }
};

struct MinimizedResult {
    DFA dfa;
    vector<vector<int>> groups;
};

class DisjointSet {
private:
    vector<int> parent;
    vector<int> rankValue;

public:
    explicit DisjointSet(int n) : parent(n), rankValue(n, 0) {
        for (int i = 0; i < n; ++i)
            parent[i] = i;
    }

    int find(int x) {
        if (parent[x] != x)
            parent[x] = find(parent[x]);
        return parent[x];
    }

    void unite(int a, int b) {
        a = find(a);
        b = find(b);

        if (a == b)
            return;

        if (rankValue[a] < rankValue[b])
            swap(a, b);

        parent[b] = a;

        if (rankValue[a] == rankValue[b])
            ++rankValue[a];
    }
};

MinimizedResult minimizeDFA(const DFA& d) {
    const int S = d.getNumStates();
    const int A = static_cast<int>(d.getAlphabet().size());

    // Add one internal Error state. It is not included in the final DFA.
    const int errorState = S;
    const int totalStates = S + 1;

    // Build a complete transition table for the table-filling algorithm.
    // Every missing transition (-1) goes to the internal Error state.
    vector<vector<int>> transitions(totalStates, vector<int>(A, errorState));

    for (int s = 0; s < S; ++s) {
        for (int a = 0; a < A; ++a) {
            int nextState = d.getTransition(s, a);
            transitions[s][a] = (nextState == -1) ? errorState : nextState;
        }
    }

    // The Error state loops to itself for every input symbol.
    for (int a = 0; a < A; ++a)
        transitions[errorState][a] = errorState;

    // The Error state is non-final.
    vector<bool> isFinal(totalStates, false);
    for (int s = 0; s < S; ++s)
        isFinal[s] = d.isFinal(s);

    // Give every unordered pair (i, j), i < j, a unique index.
    vector<vector<int>> pairIndex(totalStates, vector<int>(totalStates, -1));
    int pairCount = 0;

    for (int i = 0; i < totalStates; ++i) {
        for (int j = i + 1; j < totalStates; ++j) {
            pairIndex[i][j] = pairCount;
            pairIndex[j][i] = pairCount;
            ++pairCount;
        }
    }

    // reverseDependencies[targetPair] contains source pairs whose
    // transitions lead to targetPair for at least one input symbol.
    vector<vector<int>> reverseDependencies(pairCount);

    for (int p = 0; p < totalStates; ++p) {
        for (int q = p + 1; q < totalStates; ++q) {
            int sourcePair = pairIndex[p][q];

            for (int a = 0; a < A; ++a) {
                int r = transitions[p][a];
                int t = transitions[q][a];

                if (r == t)
                    continue;

                int targetPair = pairIndex[r][t];
                reverseDependencies[targetPair].push_back(sourcePair);
            }
        }
    }

    // Initially, every pair containing one final and one non-final state
    // is distinguishable.
    vector<bool> distinguishable(pairCount, false);
    queue<int> workQueue;

    for (int i = 0; i < totalStates; ++i) {
        for (int j = i + 1; j < totalStates; ++j) {
            if (isFinal[i] != isFinal[j]) {
                int id = pairIndex[i][j];
                distinguishable[id] = true;
                workQueue.push(id);
            }
        }
    }

    // Propagate distinguishability through reverse dependencies.
    while (!workQueue.empty()) {
        int markedPair = workQueue.front();
        workQueue.pop();

        for (int dependentPair : reverseDependencies[markedPair]) {
            if (!distinguishable[dependentPair]) {
                distinguishable[dependentPair] = true;
                workQueue.push(dependentPair);
            }
        }
    }

    // Any pair of original states not marked distinguishable is equivalent.
    // Use DSU to collect the equivalent original states into groups.
    DisjointSet dsu(S);

    for (int i = 0; i < S; ++i) {
        for (int j = i + 1; j < S; ++j) {
            int id = pairIndex[i][j];

            if (!distinguishable[id])
                dsu.unite(i, j);
        }
    }

    vector<int> rootToGroup(S, -1);
    vector<int> groupOfState(S, -1);
    vector<vector<int>> groups;

    for (int s = 0; s < S; ++s) {
        int root = dsu.find(s);

        if (rootToGroup[root] == -1) {
            rootToGroup[root] = static_cast<int>(groups.size());
            groups.push_back({});
        }

        int groupId = rootToGroup[root];
        groupOfState[s] = groupId;
        groups[groupId].push_back(s);
    }

    // Construct the minimized DFA using one representative from each group.
    const int minimizedStates = static_cast<int>(groups.size());
    DFA minimized;

    minimized.setNumStates(minimizedStates);
    minimized.setAlphabet(d.getAlphabet());
    minimized.setStartState(groupOfState[d.getStartState()]);
    minimized.setTransitionTable(
        vector<vector<int>>(minimizedStates, vector<int>(A, -1))
    );

    vector<int> finalGroups;

    for (int g = 0; g < minimizedStates; ++g) {
        int representative = groups[g][0];

        if (d.isFinal(representative))
            finalGroups.push_back(g);

        for (int a = 0; a < A; ++a) {
            int nextState = d.getTransition(representative, a);
            int minimizedNext = (nextState == -1)
                                  ? -1
                                  : groupOfState[nextState];

            minimized.setTransition(g, a, minimizedNext);
        }
    }

    minimized.setFinalStatesList(finalGroups);

    MinimizedResult result;
    result.dfa = minimized;
    result.groups = groups;
    return result;
}

void printGroupName(const vector<int>& members) {
    if (members.size() == 1) {
        cout << members[0];
        return;
    }

    cout << "{";
    for (int i = 0; i < static_cast<int>(members.size()); ++i) {
        cout << members[i];
        if (i + 1 < static_cast<int>(members.size()))
            cout << ",";
    }
    cout << "}";
}

string symbolName(char symbol) {
    if (symbol == 'L' || symbol == 'l')
        return "letter";
    if (symbol == 'D' || symbol == 'd')
        return "digit";
    return string(1, symbol);
}

void printMinimizedDFA(const DFA& dfa, const vector<vector<int>>& groups) {
    cout << "Start: ";
    printGroupName(groups[dfa.getStartState()]);
    cout << '\n';

    cout << "Final: ";
    bool firstFinal = true;

    for (int s = 0; s < dfa.getNumStates(); ++s) {
        if (dfa.isFinal(s)) {
            if (!firstFinal)
                cout << ", ";

            printGroupName(groups[s]);
            firstFinal = false;
        }
    }

    cout << '\n';

    for (int s = 0; s < dfa.getNumStates(); ++s) {
        for (int a = 0; a < static_cast<int>(dfa.getAlphabet().size()); ++a) {
            int nextState = dfa.getTransition(s, a);

            if (nextState == -1)
                continue;

            printGroupName(groups[s]);
            cout << "   ";
            printGroupName(groups[nextState]);
            cout << "   " << symbolName(dfa.getAlphabet()[a]) << '\n';
        }
    }
}

void runTest(int testNumber, const DFA& dfa, int expectedStates) {
    cout << "\n========== TEST " << testNumber << " ==========\n";

    if (!DFAvalidator::isValid(dfa)) {
        cout << "Invalid DFA!\n";
        return;
    }

    MinimizedResult minimized = minimizeDFA(dfa);

    cout << "\nMinimized DFA:\n";
    printMinimizedDFA(minimized.dfa, minimized.groups);

    cout << "\nExpected states: " << expectedStates << '\n';
    cout << "Actual states: " << minimized.dfa.getNumStates() << '\n';

    if (minimized.dfa.getNumStates() == expectedStates)
        cout << "PASS\n";
    else
        cout << "FAIL\n";
}

int main() {
    runTest(1,
        DFA(4, {'a', 'b'}, 0,
            {
                {1, 2},
                {3, 1},
                {3, 2},
                {3, 3}
            },
            {3}),
        3
    );

    runTest(2,
        DFA(5, {'a', 'b'}, 0,
            {
                {2, 1},
                {3, 1},
                {3, 2},
                {3, 4},
                {4, 4}
            },
            {4}),
        4
    );

    runTest(3,
        DFA(4, {'L', 'D'}, 0,
            {
                {1, -1},
                {2, 3},
                {2, 3},
                {2, 3}
            },
            {1, 2, 3}),
        2
    );

    runTest(4,
        DFA(3, {'a', 'b'}, 0,
            {
                {1, 2},
                {-1, 2},
                {-1, 2}
            },
            {0, 1, 2}),
        2
    );

    runTest(5,
        DFA(6, {'a', 'b'}, 0,
            {
                {1, 2},
                {4, 1},
                {4, 3},
                {4, 3},
                {4, 5},
                {5, 5}
            },
            {4, 5}),
        3
    );

    return 0;
}
