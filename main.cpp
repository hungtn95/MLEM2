/**
    CS-11
    main.cpp
    Purpose: Implementation of MLEM2 algorithm
    @author Hung Nguyen
	@assignment EECS 690 Project 1
    @date 10/7/16 
*/
#include <iostream>
#include <set>
#include <map>
#include <vector>
#include <stack>
#include <string>
#include <sstream>
#include <iomanip>
#include <algorithm>
#include <fstream>

using namespace std;

const string DO_NOT_CARE="*";
const string LOST="?";
const string ATTRIBUTE_CONCEPT="-";

typedef struct AttributeValue {
    int attribute;
    string value;
    set<int> block;
} AttributeValue;

bool isNormal(string symbol) {
    return (symbol != DO_NOT_CARE) && (symbol != LOST) && (symbol != ATTRIBUTE_CONCEPT);
}

void printSet(set<int> s) {
    cout << "[ ";
    for (int i : s) {
        cout << i << " ";
    }
    cout << "]";
    cout << '\n';
}

set<int> Difference(set<int> a, set<int> b) {
    set<int> difference;
    set_difference(a.begin(),a.end(),b.begin(),b.end(),inserter(difference,difference.begin()));  
    return difference;
}

set<int> Intersect(set<int> a, set<int> b) {
    set<int> intersect;
    set_intersection(a.begin(),a.end(),b.begin(),b.end(),inserter(intersect,intersect.begin()));  
    return intersect;
}

template <typename T>
set<T> Union(set<T> a, set<T> b) {
    set<T> Union;
    set_union(a.begin(),a.end(),b.begin(),b.end(),inserter(Union,Union.begin()));  
    return Union;
}

set<int> intersectList(vector<set<int>> list) {
    if (list.size() == 1) return list[0];
    set<int> intersect_set = list[0];
    for (int i = 1; i < list.size(); i++) {
        set<int> &ref = intersect_set;
        ref = Intersect(ref, list[i]);
    }
    return intersect_set;
}

template <typename T>
set<T> unionList(vector<set<T>> list) {
    if (list.size() == 1) return list[0];
    set<T> union_set = list[0];
    for (int i = 1; i < list.size(); i++) {
        set<T> &ref = union_set;
        ref = Union(ref, list[i]);
    }
    return union_set;
}

map<string, set<int>> findConceptBlock(vector<string*> &decision_table, int num_attributes, int num_cases) {
    int concept_index = num_attributes - 1;
    map<string, set<int>> concept_block;
    for (int i = 0; i < num_cases; i++) {
        string concept = decision_table[i][concept_index];
        if (concept_block.find(concept) == concept_block.end()) {
            set<int> v;
            v.insert(i);
            concept_block.insert(pair<string,set<int>>(concept,v));
        } else {
            concept_block[concept].insert(i);
        }
    }
    return concept_block;
}

map<string, vector<string>>* findAttributeValueConcept(vector<string*> &decision_table, int num_concepts, int num_attributes, int num_cases) {
    int concept_index = num_attributes - 1;
    map<string, vector<string>>* attribute_value_concept = new  map<string, vector<string>>[num_attributes];
    for (int i = 0; i < num_attributes; i++) {
        for (int j = 0; j < num_cases; j++) {
            if (isNormal(decision_table[j][i])) {
                string concept = decision_table[j][concept_index];
                string attribute_value = decision_table[j][i];
                if (attribute_value_concept[i].find(concept) == attribute_value_concept[i].end()) {
                    vector<string> v;
                    v.push_back(attribute_value);
                    attribute_value_concept[i].insert(pair<string,vector<string>>(concept,v));
                } else {
                    attribute_value_concept[i][concept].push_back(attribute_value);
                }
            }
        }
    }
    return attribute_value_concept;
}

vector<string> findMostFrequent(vector<string> &list) {
    vector<string> most_frequent;
    map<string,int> frequencies;
    for (string item : list) {
        if (frequencies.find(item) == frequencies.end()) {
            frequencies.insert(pair<string,int>(item,1));
        } else {
            frequencies[item]++;
        }
    }
    int max = 0;
    for (auto const&frequency : frequencies) {
        if (max <= frequency.second) {
            max = frequency.second;
        }
    }
    for (auto const&frequency : frequencies) {
        if (frequency.second == max) {
            most_frequent.push_back(frequency.first);
        }
    }
    return most_frequent;
}

map<string, set<int>>* findAttributeValuePairs(vector<string*> &decision_table, int num_attributes, int num_cases) {
    map<string, set<int>>* attribute_value_pairs = new  map<string, set<int>>[num_attributes];
    for (int i = 0; i < num_attributes; i++) {
        for (int j = 0; j < num_cases; j++) {
            string attribute_value = decision_table[j][i];
            if (isNormal(attribute_value)) {
                if (attribute_value_pairs[i].find(attribute_value) == attribute_value_pairs[i].end()) {
                    set<int> s;
                    s.insert(j);
                    attribute_value_pairs[i].insert(pair<string,set<int>>(attribute_value,s));
                } else {
                    attribute_value_pairs[i][attribute_value].insert(j);
                }
            }
        }
    }
    return attribute_value_pairs;
}

set<int> findSpecialSymbolSet(vector<string*> &decision_table, map<string, set<int>>* &attribute_value_pairs, vector<string> &case_list, set<int> universal, int attribute_index, int case_index, int num_cases) {
    string attribute_value = decision_table[case_index][attribute_index];
    if (isNormal(attribute_value)) {
        return attribute_value_pairs[attribute_index][attribute_value];
    } else if (attribute_value == DO_NOT_CARE || attribute_value == LOST) {
        return universal;
    }
    vector<set<int>> U;
    vector<string> most_frequent_attributes = findMostFrequent(case_list);
    for (auto const&attribute : most_frequent_attributes) {
        U.push_back(attribute_value_pairs[attribute_index][attribute]);
    }
    return unionList<int>(U);
}

set<int>* findCharacteristicSet(vector<string*> &decision_table, map<string, set<int>>* &attribute_value_pairs, map<string, vector<string>>* &attribute_value_concept, int num_attributes, int num_cases) {
    int concept_index = num_attributes - 1;
    string concept;
    string attribute_value;
    set<int>* characteristic_set = new set<int>[num_cases];
    for (int i = 0; i < num_attributes-1; i++) {
        for (int j = 0; j < num_cases; j++) {
            concept = decision_table[j][concept_index];
            attribute_value = decision_table[j][i];
            if (attribute_value == ATTRIBUTE_CONCEPT) {
                vector<string> most_frequent_attributes = findMostFrequent(attribute_value_concept[i][concept]);
                for (auto const&attribute : most_frequent_attributes) {
                    set<int> &ref = attribute_value_pairs[i][attribute];
                    ref.insert(j);
                }
            } else if (attribute_value == DO_NOT_CARE) {
                for (auto &attribute_value_pair : attribute_value_pairs[i]) {
                    set<int> &ref = attribute_value_pair.second;
                    ref.insert(j);
                }
            } 
        }
    }
    set<int> universal;
    for (int i = 0; i < num_cases; i++) {
        universal.insert(i);
    }
    for (int i = 0; i < num_cases; i++) {
        set<int> &ref = characteristic_set[i];
        string concept = decision_table[i][concept_index];
        vector<set<int>> set_list;
        vector<string> case_list = attribute_value_concept[0][concept];
        set_list.push_back(findSpecialSymbolSet(decision_table, attribute_value_pairs, case_list, universal, 0, i, num_cases));
        for (int j = 1; j < num_attributes-1; j++) {
            case_list = attribute_value_concept[j][concept];
            set_list.push_back(findSpecialSymbolSet(decision_table, attribute_value_pairs, case_list, universal, j, i, num_cases));
        }
        ref = intersectList(set_list);
    }
    return characteristic_set;
}

set<int> findConceptApproximationLower(set<int>* &characteristic_set, map<string, set<int>> &concept_block, string concept) {
    vector<set<int>> lower_concept_approximation;
    for (int matched_case : concept_block[concept]) {
        if (Difference(characteristic_set[matched_case], concept_block[concept]).size() == 0) {
            lower_concept_approximation.push_back(characteristic_set[matched_case]);
        }
    }
    return unionList<int>(lower_concept_approximation);
}

set<int> findConceptApproximationUpper(set<int>* &characteristic_set, map<string, set<int>> &concept_block, string concept) {
    vector<set<int>> upper_concept_approximation;
    for (int matched_case : concept_block[concept]) {
        if (Intersect(characteristic_set[matched_case], concept_block[concept]).size() != 0) {
            upper_concept_approximation.push_back(characteristic_set[matched_case]);
        }
    }
    return unionList<int>(upper_concept_approximation);
}

int compare(vector<AttributeValue> A_V, set<int> G, int t1, int t2) {
    int result = Intersect(A_V[t1].block, G).size() - Intersect(A_V[t2].block, G).size();
    if (result == 0) {
        result = A_V[t2].block.size() - A_V[t1].block.size();
        if (result == 0) {
            result = t2 - t1;
        }
    }
    return result;
}

set<int> removeCondition(set<int> T, int t) {
    set<int> copy = T;
    set<int>::iterator it = copy.find(t);
    copy.erase(t);
    return copy;
}

set<set<int>> removeRule(set<set<int>> local_covering, set<int> T) {
    set<set<int>> copy = local_covering;
    set<set<int>>::iterator it = copy.find(T);
    copy.erase(T);
    return copy;
}

vector<set<int>> transform(vector<AttributeValue> A_V, set<int> T) {
    vector<set<int>> list;
    for (int t : T) {
        list.push_back(A_V[t].block);
    }
    return list;
}

vector<set<int>> transformList(vector<AttributeValue> A_V, set<set<int>> T) {
    vector<set<int>> list;
    for (set<int> t : T) {
        list.push_back(intersectList(transform(A_V, t)));
    }
    return list;
}

set<set<int>> LEM2(vector<AttributeValue> A_V, set<int> B) {
    set<int> G = B;
    set<set<int>> local_covering;
    while (!G.empty()) {
        set<int> T;
        set<int> T_G;
        for (int i = 0; i < A_V.size(); i++) {
            if (!Intersect(A_V[i].block, G).empty()) {
                T_G.insert(i);
            }
        }
        while (T.empty() || !Difference(intersectList(transform(A_V, T)), B).empty()) {
            int max = *T_G.begin();
            for (int i : T_G) {
                if (compare(A_V, G, i, max) > 0) {
                    max = i;
                }
            }
            AttributeValue t = A_V[max];
            T.insert(max);
            G = Intersect(t.block, G);
            T_G.clear();
            for (int i = 0; i < A_V.size(); i++) {
                if (!Intersect(A_V[i].block, G).empty()) {
                    T_G.insert(i);
                }
            }
            T_G = Difference(T_G, T);
        }
        if (T.size() > 1) {
            set<int> original_rule_set = T;
            for (int t : original_rule_set) {
                set<int> new_rule_set = removeCondition(T, t);
                if (Difference(intersectList(transform(A_V, new_rule_set)), B).empty()) {
                    T = new_rule_set;
                }
            }
        }
        local_covering.insert(T);
        G = Difference(B, unionList(transformList(A_V, local_covering)));
    }
    if (local_covering.size() > 1) {
        for (set<int> T : local_covering) {
            if (unionList(transformList(A_V, removeRule(local_covering, T))) == B) {
                local_covering = removeRule(local_covering, T);
            }
        }
    }
    return local_covering;
}

int main()
{
    string ignore;
    string input;
    string rawList;
    vector<string> attributes;
    set<string> concepts;
    vector<string*> decision_table;
    int concept_index;
    int num_cases = 0;
    int num_attributes = 0;
    
    ifstream inputfile;
    inputfile.open("test.txt");

    getline(inputfile, ignore);
    getline(inputfile, rawList);
    size_t first = rawList.find("[");
    size_t last = rawList.find("]", first);
    string processedList = rawList.substr(first+1, last-first-1);
    istringstream iss(processedList);

    while (iss >> input)
    {
        attributes.push_back(input);
        num_attributes++;
    }
    concept_index = num_attributes - 1;
    
    while (!inputfile.eof()) 
    {
        getline(inputfile, input);
        string* single_case = new string[num_attributes];
        istringstream iss_case(input);
        for (int i = 0; i < num_attributes; i++) {
            iss_case >> single_case[i]; 
        }
        decision_table.push_back(single_case);
        concepts.insert(single_case[concept_index]);
        num_cases++;
    }
    inputfile.close();

    // for (string k : attributes) {
    //     cout << k << " ";
    // }
    // cout << '\n';
    // for (string* single_case : decision_table) {
    //     for (int i = 0; i < num_attributes; i++) {
    //         cout << single_case[i] << " ";
    //     }
    //     cout << '\n';
    // }

    string decision = attributes[concept_index];
    map<string, vector<string>>* attribute_value_concept = findAttributeValueConcept(decision_table, concepts.size(), num_attributes, num_cases);
    map<string, set<int>>* attribute_value_pairs = findAttributeValuePairs(decision_table, num_attributes, num_cases);
    map<string, set<int>> concept_block = findConceptBlock(decision_table, num_attributes, num_cases);
    set<int>* characteristic_set = findCharacteristicSet(decision_table, attribute_value_pairs, attribute_value_concept, num_attributes, num_cases);

    vector<AttributeValue> A_V;
    for (int i = 0; i < num_attributes - 1; i++) { 
        for (auto &attribute_value : attribute_value_pairs[i]) {
            AttributeValue t;
            t.attribute = i;
            t.value = attribute_value.first;
            t.block = attribute_value.second;
            A_V.push_back(t);
        }
    }

    set<int> B;
    set<set<int>> local_covering;
    // cout << "Possible rules: " << '\n';
    // for (string concept : concepts) {
    //     B = findConceptApproximationUpper(characteristic_set, concept_block, concept);
    //     local_covering = LEM2(A_V, B);
    //     for (set<int> T : local_covering) {
    //         string rule = "";
    //         bool check = true;
    //         for (int t : T) {
    //             if (check) {
    //                 check = false;
    //             } else {
    //                 rule += " & ";
    //             }
    //             rule += "(" + attributes[A_V[t].attribute] + ", " + A_V[t].value + ")";
    //         }
    //         rule += " -> (" + decision + ", " + concept + ")";
    //         cout << rule << '\n';
    //     }
    // }
    cout << "Certain rules: " << '\n';
    for (string concept : concepts) {
        B = findConceptApproximationLower(characteristic_set, concept_block, concept);
        local_covering = LEM2(A_V, B);
        for (set<int> T : local_covering) {
            string rule = "";
            bool check = true;
            for (int t : T) {
                if (check) {
                    check = false;
                } else {
                    rule += " & ";
                }
                rule += "(" + attributes[A_V[t].attribute] + ", " + A_V[t].value + ")";
            }
            rule += " -> (" + decision + ", " + concept + ")";
            cout << rule << '\n';
        }
    }
    return 0;
}