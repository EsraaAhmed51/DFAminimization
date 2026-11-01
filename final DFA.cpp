
#include <iostream>
#include <vector>
#include <map>
#include <unordered_map>
#include <algorithm>
#include <functional>
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


// Custom hash for vector<int>
struct VectorHash {
    size_t operator()(const vector<int>& v) const {
        size_t hashValue = 0;
        for (int x : v) {
            hashValue ^= hash<int>()(x) +
                         0x9e3779b9 +
                         (hashValue << 6) +
                         (hashValue >> 2);
        }
        return hashValue;
    }
};

struct PairHash {
    size_t operator()(const pair<int, vector<int>>& p) const {
        size_t h1 = hash<int>()(p.first);
        size_t h2 = VectorHash()(p.second);

        return h1 ^ (h2 + 0x9e3779b9 + (h1 << 6) + (h1 >> 2));
    }
};

class DFAvalidator {
public:
    static bool isValid(const DFA& dfa) {

        int numStates = dfa.getNumStates();
        vector<char> alphabet = dfa.getAlphabet();
        int startState = dfa.getStartState();
        vector<vector<int>> transitionTable =
            dfa.getTransitionTable();

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

        if (transitionTable.size() != numStates)
            return false;

        for (const auto& row : transitionTable) {
            if (row.size() != alphabet.size())
                return false;

            for (int state : row) {
                if (state < 0 || state >= numStates)
                    return false;
            }
        }

        return true;
    }
};


DFA minimizeDFA(const DFA& d) {

    const int S = d.getNumStates();
    const int A = d.getAlphabet().size();

    vector<int> group(S);

    // Initial partition: final and non-final states
    for (int s = 0; s < S; ++s)
        group[s] = d.isFinal(s) ? 1 : 0;


    // Compress IDs to 0..k-1
    {
        unordered_map<int, int> remap;
        int k = 0;

        for (int s = 0; s < S; ++s) {
            auto it = remap.find(group[s]);

            if (it == remap.end())
                remap[group[s]] = k++;

            group[s] = remap[group[s]];
        }
    }

    int numGroups =
        *max_element(group.begin(), group.end()) + 1;

    while (true) {

        unordered_map<pair<int, vector<int>>, int, PairHash>
            sigToId;

        vector<int> newGroup(S);
        int newNumGroups = 0;

        for (int s = 0; s < S; ++s) {

            vector<int> sig(A);

            for (int a = 0; a < A; ++a)
                sig[a] = group[d.getTransition(s, a)];

            auto key = make_pair(group[s], sig);

            auto it = sigToId.find(key);

            if (it == sigToId.end()) {
                sigToId[key] = newNumGroups;
                newGroup[s] = newNumGroups++;
            }
            else {
                newGroup[s] = it->second;
            }
        }

        if (newNumGroups == numGroups) {
            group.swap(newGroup);
            break;
        }

        group.swap(newGroup);
        numGroups = newNumGroups;
    }
    // Construct minimized DFA
    DFA m;

    m.setNumStates(numGroups);
    m.setAlphabet(d.getAlphabet());

    m.setTransitionTable(
        vector<vector<int>>(numGroups, vector<int>(A, 0))
    );

    m.setStartState(group[d.getStartState()]);

    vector<bool> isFinBlock(numGroups, false);

    for (int s = 0; s < S; ++s) {

        int g = group[s];

        if (d.isFinal(s))
            isFinBlock[g] = true;

        for (int a = 0; a < A; ++a)
            m.setTransition(
                g, a,
                group[d.getTransition(s, a)]
            );
    }

    vector<int> finals;

    for (int g = 0; g < numGroups; ++g) {
        if (isFinBlock[g])
            finals.push_back(g);
    }

    m.setFinalStatesList(finals);

    return m;
}


void printDFA(const DFA& dfa) {

    cout << "Number of states: "
         << dfa.getNumStates() << '\n';

    cout << "Start state: "
         << dfa.getStartState() << '\n';

    cout << "Final states: ";

    for (int s : dfa.getFinalStates())
        cout << s << " ";

    cout << '\n';

    cout << "\nTransition table:\n";
    cout << "State\t";

    for (char c : dfa.getAlphabet())
        cout << c << "\t";

    cout << '\n';

    for (int s = 0; s < dfa.getNumStates(); ++s) {

        cout << s << "\t";

        for (int a = 0; a < dfa.getAlphabet().size(); ++a)
            cout << dfa.getTransition(s, a) << "\t";

        cout << '\n';
    }
}


void runTest(int testNumber, const DFA& dfa, int expectedStates) {

    cout << "\n========== TEST "
         << testNumber << " ==========\n";

    if (!DFAvalidator::isValid(dfa)) {
        cout << "Invalid DFA!\n";
        return;
    }

    cout << "Original DFA:\n";
    printDFA(dfa);

    DFA minimized = minimizeDFA(dfa);

    cout << "\nMinimized DFA:\n";
    printDFA(minimized);

    cout << "\nExpected states: " << expectedStates << '\n';

    cout << "Actual states: "
         << minimized.getNumStates() << '\n';

    if (minimized.getNumStates() == expectedStates)
        cout << "PASS\n";
    else
        cout << "FAIL\n";
}


// Keep your original main() and all 14 test cases here.


int main() {

    // Test 1: All states equivalent
    runTest(1,
        DFA(3, {'a', 'b'}, 0,
            {
                {0, 0},
                {1, 1},
                {2, 2}
            },
            {}),
        1
    );

    // Test 2: All states distinguishable
    runTest(2,
        DFA(3, {'a', 'b'}, 0,
            {
                {1, 0},
                {2, 1},
                {2, 2}
            },
            {2}),
        3
    );

    // Test 3: Two equivalent non-final states
    runTest(3,
        DFA(3, {'a', 'b'}, 0,
            {
                {1, 2},
                {1, 2},
                {2, 2}
            },
            {2}),
        2
    );

    // Test 4: Two equivalent final states
    runTest(4,
        DFA(3, {'a', 'b'}, 0,
            {
                {1, 2},
                {1, 1},
                {1, 1}
            },
            {1, 2}),
        2
    );

    // Test 5: Multiple refinement iterations
    runTest(5,
        DFA(4, {'a', 'b'}, 0,
            {
                {1, 0},
                {2, 1},
                {3, 2},
                {3, 3}
            },
            {3}),
        4
    );

    // Test 6: Unreachable state
    runTest(6,
        DFA(3, {'a'}, 0,
            {
                {1},
                {1},
                {2}
            },
            {1}),
        3
    );
     // Test 7: One non-final state
    runTest(7,
        DFA(1, {'a', 'b'}, 0,
            {
                {0, 0}
            },
            {}),
        1
    );

    // Test 8: One final state
    runTest(8,
        DFA(1, {'a', 'b'}, 0,
            {
                {0, 0}
            },
            {0}),
        1
    );

    // Test 9: No final states
    runTest(9,
        DFA(4, {'a', 'b'}, 0,
            {
                {1, 2},
                {2, 3},
                {3, 0},
                {0, 1}
            },
            {}),
        1
    );

    // Test 10: All states are final
    runTest(10,
        DFA(4, {'a', 'b'}, 0,
            {
                {1, 2},
                {2, 3},
                {3, 0},
                {0, 1}
            },
            {0, 1, 2, 3}),
        1
    );

    // Test 11: Unreachable final states
    runTest(11,
        DFA(4, {'a', 'b'}, 0,
            {
                {1, 0},
                {1, 1},
                {2, 2},
                {3, 3}
            },
            {2, 3}),
        2
    );

    // Test 12: Start state is final
    runTest(12,
        DFA(3, {'a', 'b'}, 0,
            {
                {1, 2},
                {1, 1},
                {2, 2}
            },
            {0, 1}),
        3
    );

    // Test 13: Multiple equivalent groups
    runTest(13,
        DFA(6, {'a', 'b'}, 0,
            {
                {2, 4},
                {2, 4},
                {2, 4},
                {3, 5},
                {3, 5},
                {3, 5}
            },
            {3, 4, 5}),
        2
    );

    // Test 14: Three alphabet symbols
    runTest(14,
    DFA(5, {'a', 'b', 'c'}, 0,
        {
            {1, 2, 3},
            {1, 2, 3},
            {1, 2, 3},
            {4, 4, 4},
            {4, 4, 4}
        },
        {3, 4}),
    2
);
    // Test 15: Four alphabet symbols
    runTest(15,
        DFA(3, {'a', 'b', 'c', 'd'}, 0,
            {
                {1, 2, 1, 2},
                {1, 2, 1, 2},
                {2, 2, 2, 2}
            },
            {2}),
        2
    );
    

    return 0;
}
