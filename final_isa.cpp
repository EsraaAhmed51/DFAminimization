

#include <iostream>
#include <vector>
#include <map>
#include <unordered_map>
#include <algorithm>
#include <functional>
#include <string>
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
          alphabet(alphabet),   transitionTable(transitionTable),
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
        for (int x : v)
{
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

        for (int finalState : dfa.getFinalStates())
{
            if (finalState < 0 || finalState >= numStates)
                return false;
        }

        if (transitionTable.size() != numStates)
            return false;

        for (const auto& row : transitionTable)
{
            if (row.size() != alphabet.size())
                return false;

            for (int state : row)
{
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

MinimizedResult minimizeDFA(const DFA& d) {

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

        for (int s = 0; s < S; ++s)
{
            auto it = remap.find(group[s]);

            if (it == remap.end())
                remap[group[s]] = k++;

            group[s] = remap[group[s]];
        }
    }

    int numGroups =
        *max_element(group.begin(), group.end()) + 1;

    while (true)
{
        unordered_map<pair<int, vector<int>>, int, PairHash>
            sigToId;

        vector<int> newGroup(S);
        int newNumGroups = 0;

        for (int s = 0; s < S; ++s)
{
            vector<int> sig(A);

            for (int a = 0; a < A; ++a)
{
                int nextState = d.getTransition(s, a);
                sig[a] = (nextState == -1) ? -1 : group[nextState];
            }

            auto key = make_pair(group[s], sig);

            auto it = sigToId.find(key);

            if (it == sigToId.end())
{
                sigToId[key] = newNumGroups;
                newGroup[s] = newNumGroups++;
            }
            else
{
                newGroup[s] = it->second;
            }
        }

        if (newNumGroups == numGroups)
{
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

    for (int s = 0; s < S; ++s)
{
        int g = group[s];

        if (d.isFinal(s))
            isFinBlock[g] = true;

        for (int a = 0; a < A; ++a)
{
            int nextState = d.getTransition(s, a);
            m.setTransition(
                g, a,
                (nextState == -1) ? -1 : group[nextState]
            );
        }
    }

    vector<int> finals;

    for (int g = 0; g < numGroups; ++g)
{
        if (isFinBlock[g])
            finals.push_back(g);
    }

    m.setFinalStatesList(finals);

    MinimizedResult result;
    result.dfa = m;
    result.groups.resize(numGroups);

    for (int s = 0; s < S; ++s)
        result.groups[group[s]].push_back(s);

    return result;
}

void printDFA(const DFA& dfa) {

    for (int s = 0; s < dfa.getNumStates(); s++)
{
        cout << "{" << s << "} {";

        bool first = true;
        for (int a = 0; a < dfa.getAlphabet().size(); a++)
{
            int nextState = dfa.getTransition(s, a);
            if (nextState == -1)
                continue;

            if (!first)
                cout << ",";
            cout << nextState;
            first = false;
        }

        cout << "} {";

        first = true;
        for (int a = 0; a < dfa.getAlphabet().size(); a++)
{
            if (dfa.getTransition(s, a) == -1)
                continue;

            if (!first)
                cout << ",";
            cout << dfa.getAlphabet()[a];
            first = false;
        }

        cout << "}" << endl;
    }
}


void printGroupName(const vector<int>& members) {
    if (members.size() == 1)
{
        cout << members[0];
        return;
    }

    cout << "{";
    for (int i = 0; i < members.size(); ++i)
{
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

void printMinimizedDFA(const DFA& dfa, const vector<vector<int>>& groups) {
    cout << "Start: ";
    printGroupName(groups[dfa.getStartState()]);
    cout << '\n';

    cout << "Final: ";
    bool firstFinal = true;
    for (int s = 0; s < dfa.getNumStates(); ++s)
{
        if (dfa.isFinal(s))
{
            if (!firstFinal)
                cout << ", ";
            printGroupName(groups[s]);
            firstFinal = false;
        }
    }
    cout << '\n';

    for (int s = 0; s < dfa.getNumStates(); ++s)
{
        for (int a = 0; a < dfa.getAlphabet().size(); ++a)
{
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

    cout << "\n========== TEST "
         << testNumber << " ==========\n";

    if (!DFAvalidator::isValid(dfa))
{
        cout << "Invalid DFA!\n";
        return;
    }

    MinimizedResult minimized = minimizeDFA(dfa);

    cout << "\nMinimized DFA:\n";
    printMinimizedDFA(minimized.dfa, minimized.groups);

    cout << "\nExpected states: " << expectedStates << '\n';

    cout << "Actual states: "
         << minimized.dfa.getNumStates() << '\n';

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

    return 0;
}
