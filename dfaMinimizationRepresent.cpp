#include <bits/stdc++.h>
using namespace std;

class DFA {
private:
    int numStates;
    int startState;
    vector<char> alphabet;
    vector<vector<int>> transitionTable;
    vector<int> FinalStates;
public:
    DFA(int n, vector<char> alphabet, int startState, vector<vector<int>> transitionTable, vector<int> FinalStates)
        : numStates(n), startState(startState), alphabet(alphabet), transitionTable(transitionTable), FinalStates(FinalStates) {}

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
        return find(FinalStates.begin(), FinalStates.end(), state) != FinalStates.end();
    }
    int getTransition(int state, int symbolIndex) const {
        return transitionTable[state][symbolIndex];
    }
    vector<vector<int>> getTransitionTable() const {
        return transitionTable;
    }
};

class DFAvalidator {
public:
    static bool isValid(const DFA& dfa) {

        int numStates = dfa.getNumStates();
        vector<char> alphabet = dfa.getAlphabet();
        int startState = dfa.getStartState();
        vector<vector<int>> transitionTable = dfa.getTransitionTable();

        if (numStates <= 0) {
            return false;
        }
        if (alphabet.empty()) {
            return false;
        }
        if (startState < 0 || startState >= numStates) {
            return false;
        }
        for (int finalState : dfa.getFinalStates()) {
            if (finalState < 0 || finalState >= numStates) {
                return false;
            }
        }
        if (transitionTable.size() != numStates) {
            return false;
        }
        for (const auto& row : transitionTable) {
            if (row.size() != alphabet.size()) {
                return false;
            }
            for (int state : row) {
                if (state < 0 || state >= numStates) {
                    return false;
                }
            }
        }

        return true;
    }
};


int main() {

    // Test 1: Valid DFA
    cout << "Test 1: Valid DFA\n";

    vector<char> alphabet = {'a', 'b'};

    vector<vector<int>> transitions = {
        {1, 2},
        {0, 2},
        {2, 1}
    };

    vector<int> finals = {1};

    DFA dfa1(3, alphabet, 0, transitions, finals);

    cout << (DFAvalidator::isValid(dfa1)
             ? "Valid DFA"
             : "Invalid DFA") << "\n\n";


    // Test 2: Invalid number of states
    cout << "Test 2: Invalid number of states\n";

    DFA dfa2(0, alphabet, 0, transitions, finals);

    cout << (DFAvalidator::isValid(dfa2)
             ? "Valid DFA"
             : "Invalid DFA") << "\n\n";


    // Test 3: Invalid start state
    cout << "Test 3: Invalid start state\n";

    DFA dfa3(3, alphabet, 5, transitions, finals);

    cout << (DFAvalidator::isValid(dfa3)
             ? "Valid DFA"
             : "Invalid DFA") << "\n\n";


    // Test 4: Invalid final state
    cout << "Test 4: Invalid final state\n";

    vector<int> invalidFinals = {1, 5};

    DFA dfa4(3, alphabet, 0, transitions, invalidFinals);

    cout << (DFAvalidator::isValid(dfa4)
             ? "Valid DFA"
             : "Invalid DFA") << "\n\n";


    // Test 5: Invalid transition destination
    cout << "Test 5: Invalid transition\n";

    vector<vector<int>> invalidTransitions = {
        {1, 2},
        {0, 5},
        {2, 1}
    };

    DFA dfa5(3, alphabet, 0, invalidTransitions, finals);

    cout << (DFAvalidator::isValid(dfa5)
             ? "Valid DFA"
             : "Invalid DFA") << "\n\n";


    // Test 6: Incorrect transition table dimensions
    cout << "Test 6: Incorrect transition table dimensions\n";

    vector<vector<int>> wrongDimensions = {
        {1, 2},
        {0},
        {2, 1}
    };

    DFA dfa6(3, alphabet, 0, wrongDimensions, finals);

    cout << (DFAvalidator::isValid(dfa6)
             ? "Valid DFA"
             : "Invalid DFA") << "\n\n";


    // Test 7: Empty alphabet
    cout << "Test 7: Empty alphabet\n";

    vector<char> emptyAlphabet;

    vector<vector<int>> emptyTransitions = {
        {},
        {},
        {}
    };

    DFA dfa7(3, emptyAlphabet, 0, emptyTransitions, finals);

    cout << (DFAvalidator::isValid(dfa7)
             ? "Valid DFA"
             : "Invalid DFA") << "\n\n";


    return 0;
}
