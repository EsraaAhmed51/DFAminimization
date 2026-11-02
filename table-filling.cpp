#include <iostream>
#include <vector>
#include <queue>
#include <algorithm>
#include <string>

using namespace std;

// =============================================
// DFA CLASS
// =============================================

class DFA {
private:
    int numStates;
    int startState;
    vector<char> alphabet;
    vector<vector<int>> transitionTable;
    vector<int> finalStates;

public:
    DFA() : numStates(0), startState(0) {}

    DFA(int n,
        vector<char> alphabet,
        int startState,
        vector<vector<int>> transitionTable,
        vector<int> finalStates)
        : numStates(n),
          startState(startState),
          alphabet(alphabet),
          transitionTable(transitionTable),
          finalStates(finalStates) {}

    int getNumStates() const {
        return numStates;
    }

    int getStartState() const {
        return startState;
    }

    vector<char> getAlphabet() const {
        return alphabet;
    }

    vector<int> getFinalStates() const {
        return finalStates;
    }

    int getTransition(int state, int symbolIndex) const {
        return transitionTable[state][symbolIndex];
    }

    vector<vector<int>> getTransitionTable() const {
        return transitionTable;
    }

    bool isFinal(int state) const {
        return find(finalStates.begin(),
                    finalStates.end(),
                    state) != finalStates.end();
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

    void setTransitionTable(const vector<vector<int>>& t) {
        transitionTable = t;
    }

    void setFinalStatesList(const vector<int>& f) {
        finalStates = f;
    }
};

// =============================================
// DFA VALIDATOR
// =============================================

class DFAValidator {
public:
    static bool isValid(const DFA& dfa) {

        int n = dfa.getNumStates();
        int start = dfa.getStartState();

        vector<char> alphabet = dfa.getAlphabet();
        vector<vector<int>> table = dfa.getTransitionTable();

        if (n <= 0)
            return false;

        if (alphabet.empty())
            return false;

        if (start < 0 || start >= n)
            return false;

        if (table.size() != n)
            return false;

        for (int f : dfa.getFinalStates()) {
            if (f < 0 || f >= n)
                return false;
        }

        for (const auto& row : table) {

            if (row.size() != alphabet.size())
                return false;

            for (int next : row) {
                if (next < 0 || next >= n)
                    return false;
            }
        }

        return true;
    }
};

// =============================================
// MINIMIZATION RESULT STRUCT
// =============================================

struct MinimizedResult {
    DFA dfa;
    vector<vector<int>> groups;

    MinimizedResult(DFA d, vector<vector<int>> g)
        : dfa(d), groups(g) {}
};

// =============================================
// OPTIMIZED TABLE-FILLING ALGORITHM
// =============================================

MinimizedResult minimizeDFA(const DFA& d) {

    int n = d.getNumStates();
    int A = d.getAlphabet().size();

    // -----------------------------------------
    // STEP 1: Find reachable states
    // -----------------------------------------

    vector<bool> reachable(n, false);
    vector<int> reachableStates;

    queue<int> q;

    int start = d.getStartState();

    q.push(start);
    reachable[start] = true;

    while (!q.empty()) {

        int u = q.front();
        q.pop();

        reachableStates.push_back(u);

        for (int a = 0; a < A; a++) {

            int v = d.getTransition(u, a);

            if (!reachable[v]) {
                reachable[v] = true;
                q.push(v);
            }
        }
    }

    int R = reachableStates.size();

    // Original state -> reachable-state index
    vector<int> id(n, -1);

    for (int i = 0; i < R; i++)
        id[reachableStates[i]] = i;

    // -----------------------------------------
    // STEP 2: Build reachable DFA
    // -----------------------------------------

    vector<vector<int>> trans(R, vector<int>(A));
    vector<bool> isFinal(R, false);

    for (int i = 0; i < R; i++) {

        int originalState = reachableStates[i];

        isFinal[i] = d.isFinal(originalState);

        for (int a = 0; a < A; a++) {

            int originalNext =
                d.getTransition(originalState, a);

            trans[i][a] = id[originalNext];
        }
    }

    // -----------------------------------------
    // STEP 3: Initialize table
    // -----------------------------------------

    // marked[i][j] = true means distinguishable
    vector<vector<bool>> marked(
        R, vector<bool>(R, false)
    );

    // dependencies[x][y] contains pairs whose
    // distinguishability depends on pair (x,y)
    vector<vector<vector<pair<int, int>>>> dependencies(
        R, vector<vector<pair<int, int>>>(R)
    );

    queue<pair<int, int>> worklist;

    // Mark final vs non-final pairs
    for (int i = 0; i < R; i++) {

        for (int j = i + 1; j < R; j++) {

            if (isFinal[i] != isFinal[j]) {

                marked[i][j] = true;
                worklist.push({i, j});
            }
        }
    }

    // -----------------------------------------
    // STEP 4: Build dependency graph
    // -----------------------------------------

    for (int i = 0; i < R; i++) {

        for (int j = i + 1; j < R; j++) {

            for (int a = 0; a < A; a++) {

                int x = trans[i][a];
                int y = trans[j][a];

                // Same destination means no dependency
                if (x == y)
                    continue;

                // Ensure x < y
                if (x > y)
                    swap(x, y);

                dependencies[x][y].push_back({i, j});
            }
        }
    }

    // -----------------------------------------
    // STEP 5: Propagate distinguishability
    // -----------------------------------------

    while (!worklist.empty()) {

        pair<int, int> current = worklist.front();
        worklist.pop();

        int x = current.first;
        int y = current.second;

        for (auto dependent : dependencies[x][y]) {

            int i = dependent.first;
            int j = dependent.second;

            if (!marked[i][j]) {

                marked[i][j] = true;

                worklist.push({i, j});
            }
        }
    }

    // -----------------------------------------
    // STEP 6: Create equivalence classes
    // -----------------------------------------

    vector<int> group(R, -1);

    int numGroups = 0;

    for (int i = 0; i < R; i++) {

        if (group[i] != -1)
            continue;

        group[i] = numGroups;

        for (int j = i + 1; j < R; j++) {

            if (!marked[i][j])
                group[j] = numGroups;
        }

        numGroups++;
    }

    // -----------------------------------------
    // STEP 7: Construct minimized DFA
    // -----------------------------------------

    vector<vector<int>> newTransitionTable(
        numGroups, vector<int>(A, 0)
    );

    vector<bool> newFinal(numGroups, false);

    for (int s = 0; s < R; s++) {

        int g = group[s];

        if (isFinal[s])
            newFinal[g] = true;

        for (int a = 0; a < A; a++) {

            int next = trans[s][a];

            newTransitionTable[g][a] = group[next];
        }
    }

    vector<int> newFinalStates;

    for (int g = 0; g < numGroups; g++) {

        if (newFinal[g])
            newFinalStates.push_back(g);
    }

    DFA result;

    result.setNumStates(numGroups);
    result.setAlphabet(d.getAlphabet());

    result.setStartState(
        group[id[d.getStartState()]]
    );

    result.setTransitionTable(newTransitionTable);
    result.setFinalStatesList(newFinalStates);

    // Original states -> minimized states
    vector<int> stateMapping(n, -1);

    for (int s = 0; s < n; s++) {

        if (reachable[s])
            stateMapping[s] = group[id[s]];
    }

    // Store original state members of each minimized group
    vector<vector<int>> groups(numGroups);

    for (int s = 0; s < R; s++) {
        groups[group[s]].push_back(reachableStates[s]);
    }

    return MinimizedResult(result, groups);
}

// =============================================
// PRINT DFA
// =============================================


void printGroupName(const vector<int>& members) {

    if (members.size() == 1) {
        cout << members[0];
        return;
    }

    cout << "{";

    for (int i = 0; i < members.size(); i++) {
        cout << members[i];

        if (i + 1 < members.size())
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

void printMinimizedDFA(
    const DFA& dfa,
    const vector<vector<int>>& groups) {

    cout << "Start: ";

    printGroupName(groups[dfa.getStartState()]);

    cout << '\n';

    cout << "Final: ";

    bool firstFinal = true;

    for (int s = 0; s < dfa.getNumStates(); s++) {

        if (dfa.isFinal(s)) {

            if (!firstFinal)
                cout << ", ";

            printGroupName(groups[s]);

            firstFinal = false;
        }
    }

    cout << '\n';

    for (int s = 0; s < dfa.getNumStates(); s++) {

        for (int a = 0; a < dfa.getAlphabet().size(); a++) {

            int nextState = dfa.getTransition(s, a);

            if (nextState == -1)
                continue;

            printGroupName(groups[s]);

            cout << "   ";

            printGroupName(groups[nextState]);

            cout << "   "
                 << symbolName(dfa.getAlphabet()[a])
                 << '\n';
        }
    }
}

void runTest(
    int testNumber,
    const DFA& dfa,
    int expectedStates) {

    cout << "\n========== TEST "
         << testNumber << " ==========\n";

    if (!DFAValidator::isValid(dfa)) {
        cout << "Invalid DFA!\n";
        return;
    }

    MinimizedResult minimized = minimizeDFA(dfa);

    cout << "\nMinimized DFA:\n";

    printMinimizedDFA(
        minimized.dfa,
        minimized.groups
    );

    cout << "\nExpected states: "
         << expectedStates << '\n';

    cout << "Actual states: "
         << minimized.dfa.getNumStates() << '\n';

    if (minimized.dfa.getNumStates() == expectedStates)
        cout << "PASS\n";
    else
        cout << "FAIL\n";
}

// =============================================
// MAIN
// =============================================
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

    return 0;
}