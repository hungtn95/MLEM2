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
#include <string>
#include <sstream>
#include <iomanip>
#include <algorithm>
#include <fstream>
#include <cmath>

using namespace std;

const string DO_NOT_CARE="*";
const string LOST="?";
const string ATTRIBUTE_CONCEPT="-";

typedef struct AttributeValue {
    int attribute;
    string value;
    set<int> block;
} AttributeValue;

typedef struct Interval {
    double lower;
    double upper;
    string toString() {
        stringstream ss;
        ss << lower << ".." << upper;
        return ss.str();
    }
} Interval;

string doubleToString(double d) {
    stringstream ss;
    ss << d;
    return ss.str();
}

double round(double y) {
    return floor(y * 10.0) / 10.0;
}

bool isNormal(string symbol) {
    return (symbol != DO_NOT_CARE) && (symbol != LOST) && (symbol != ATTRIBUTE_CONCEPT);
}

template <typename T>
void printSet(set<T> s) {
    cout << "[ ";
    for (T i : s) {
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

bool isNumerical(const char* str) {
    char* endptr = 0;
    strtod(str, &endptr);

    if(*endptr != '\0' || endptr == str)
        return false;
    return true;
}

bool isNumericalAttribute(vector<string*> &decision_table, int attribute_index, int num_cases) {
    for (int i = 0; i < num_cases; i++) {
        string value = decision_table[i][attribute_index];
        if (isNormal(value)) {
            return isNumerical(value.c_str());
        }
    }
    return false;
}

void insertAttributeValue(map<string, set<int>> &attribute, string value, int j) {
    if (attribute.find(value) == attribute.end()) {
        set<int> s;
        s.insert(j);
        attribute.insert(pair<string,set<int>>(value,s));
    } else {
        attribute[value].insert(j);
    }
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
    int concept_index = num_attributes-1;
    map<string, vector<string>>* attribute_value_concept = new  map<string, vector<string>>[num_attributes-1];
    for (int i = 0; i < num_attributes-1; i++) {
        for (int j = 0; j < num_cases; j++) {
            string attribute_value = decision_table[j][i];
            string concept = decision_table[j][concept_index];
            if (isNormal(attribute_value)) {
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

map<string, set<int>>* findAttributeValuePairs(vector<string*> &decision_table, map<int,map<double,vector<string>>> &interval_map, int num_attributes, int num_cases) {
    map<string, set<int>>* attribute_value_pairs = new  map<string, set<int>>[num_attributes];
    for (int i = 0; i < num_attributes-1; i++) {
        if (isNumericalAttribute(decision_table, i, num_cases)) {
            set<double> a;
            for (int j = 0; j < num_cases; j++) {
                a.insert(stod(decision_table[j][i].c_str()));
            }  
            vector<double> b(a.begin(), a.end()); 
            vector<double> cut_points;
            for (int j = 0; j < b.size() - 1; j++) {
                cut_points.push_back((b[j]+b[j+1])/2);
            }  
            vector<Interval> primary_intervals;
            for (double cut_point : cut_points) {
                Interval i1;
                i1.lower = b[0];
                i1.upper = cut_point;
                primary_intervals.push_back(i1);
                Interval i2;
                i2.lower = cut_point;
                i2.upper = b[b.size()-1];
                primary_intervals.push_back(i2);
            }
            for (double value : a) {
                for (Interval interval : primary_intervals) {
                    if (value >= interval.lower && value <= interval.upper) {
                        interval_map[i][value].push_back(interval.toString());
                    }        
                }
            }
            for (int j = 0; j < num_cases; j++) {
                double value = stod(decision_table[j][i].c_str());
                for (Interval interval : primary_intervals) {
                    if (value >= interval.lower && value <= interval.upper) {
                        insertAttributeValue(attribute_value_pairs[i], interval.toString(), j);
                    }
                }
            }  
        } else {
            for (int j = 0; j < num_cases; j++) {
                string attribute_value = decision_table[j][i];
                if (isNormal(attribute_value)) {
                    insertAttributeValue(attribute_value_pairs[i], attribute_value, j);
                }
            }
        }
    }
    return attribute_value_pairs;
}

set<int> findSpecialSymbolSet(vector<string*> &decision_table, map<string, set<int>>* &attribute_value_pairs, map<int,map<double,vector<string>>> &interval_map, vector<string> &case_list, set<int> universal, int attribute_index, int case_index, int num_cases) {
    string attribute_value = decision_table[case_index][attribute_index];
    map<string, set<int>> map = attribute_value_pairs[attribute_index];
    vector<set<int>> U;
    if (isNumerical(attribute_value.c_str())) {
        vector<string> intervals = interval_map[attribute_index][stod(attribute_value.c_str())];
        for (string interval : intervals) {
            U.push_back(map[interval]);
        }
        return intersectList(U);
    } else if (isNormal(attribute_value)) {
        return map[attribute_value];
    } else if (attribute_value == DO_NOT_CARE || attribute_value == LOST) {
        return universal;
    }
    vector<string> most_frequent_attributes = findMostFrequent(case_list);
    for (auto const&attribute : most_frequent_attributes) {
        U.push_back(map[attribute]);
    }
    return unionList<int>(U);
}

set<int>* findCharacteristicSet(vector<string*> &decision_table, map<string, set<int>>* &attribute_value_pairs, map<int, map<double, vector<string>>> &interval_map, int num_concepts, int num_attributes, int num_cases) {
    int concept_index = num_attributes-1;
    string concept;
    string attribute_value;
    set<int>* characteristic_set = new set<int>[num_cases];
    map<string, vector<string>>* attribute_value_concept = findAttributeValueConcept(decision_table, num_concepts, num_attributes, num_cases);
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
        cout << "Case: " << i << '\n';
        set<int> &ref = characteristic_set[i];
        string concept = decision_table[i][concept_index];
        vector<set<int>> set_list;
        vector<string> case_list = attribute_value_concept[0][concept];
        set<int> a = findSpecialSymbolSet(decision_table, attribute_value_pairs, interval_map, case_list, universal, 0, i, num_cases);
        set_list.push_back(a);
        for (int j = 1; j < num_attributes-1; j++) {
            case_list = attribute_value_concept[j][concept];
            a = findSpecialSymbolSet(decision_table, attribute_value_pairs, interval_map, case_list, universal, j, i, num_cases);
            set_list.push_back(a);
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

int compare(vector<AttributeValue> &A_V, set<int> G, int t1, int t2) {
    int result = Intersect(A_V[t1].block, G).size() - Intersect(A_V[t2].block, G).size();
    if (result == 0) {
        result = A_V[t2].block.size() - A_V[t1].block.size();
        if (result == 0) {
            result = t2 - t1;
        }
    }
    return result;
}

set<int> removeCondition(set<int> &T, int t) {
    set<int> copy = T;
    set<int>::iterator it = copy.find(t);
    copy.erase(t);
    return copy;
}

set<set<int>> removeRule(set<set<int>> &local_covering, set<int> &T) {
    set<set<int>> copy = local_covering;
    set<set<int>>::iterator it = copy.find(T);
    copy.erase(T);
    return copy;
}

vector<set<int>> transform(vector<AttributeValue> &A_V, set<int> &T) {
    vector<set<int>> list;
    for (int t : T) {
        list.push_back(A_V[t].block);
    }
    return list;
}

vector<set<int>> transformList(vector<AttributeValue> &A_V, set<set<int>> T) {
    vector<set<int>> list;
    for (set<int> t : T) {
        list.push_back(intersectList(transform(A_V, t)));
    }
    return list;
}

set<set<int>> LEM2(vector<AttributeValue> &A_V, set<int> B) {
    set<int> G = B;
    set<set<int>> local_covering;
    int count = 0;
    while (!G.empty()) {
        cout << "Iteration: " << count << '\n';
        count++;
        int count2 = 0;
        set<int> T;
        set<int> T_G;
        for (int i = 0; i < A_V.size(); i++) {
            if (!Intersect(A_V[i].block, G).empty()) {
                T_G.insert(i);
            }
        }
        while (T.empty() || !Difference(intersectList(transform(A_V, T)), B).empty()) {
            cout << "Sub Iteration: " << count2 << '\n';
            count2++;
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

void parseInput(ifstream &inputfile, vector<string*> &decision_table, vector<string> &attributes, set<string> &concepts, int &num_cases, int &num_attributes) {
    string ignore;
    string input;
    string rawList;
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
    while (!inputfile.eof()) 
    {
        getline(inputfile, input);
        string* single_case = new string[num_attributes];
        istringstream iss_case(input);
        for (int i = 0; i < num_attributes; i++) {
            iss_case >> single_case[i]; 
        }
        decision_table.push_back(single_case);
        concepts.insert(single_case[num_attributes - 1]);
        num_cases++;
    }
    inputfile.close();
}

void run(vector<string*> &decision_table, vector<string> &attributes, set<string> &concepts, int &num_cases, int &num_attributes) {
    int concept_index = num_attributes - 1;
    string decision = attributes[concept_index];
    cout << "Finding attribute value pairs!" << '\n';
    map<int,map<double,vector<string>>> interval_map;
    map<string, set<int>>* attribute_value_pairs = findAttributeValuePairs(decision_table, interval_map, num_attributes, num_cases);
    map<string, set<int>> concept_block = findConceptBlock(decision_table, num_attributes, num_cases);
    cout << "Finding characteristic set!" << '\n';
    set<int>* characteristic_set = findCharacteristicSet(decision_table, attribute_value_pairs, interval_map, concepts.size(), num_attributes, num_cases);
    vector<AttributeValue> A_V;
    for (int i = 0; i < num_attributes-1; i++) { 
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
    cout << "Possible rules: " << '\n';
    for (string concept : concepts) {
        B = findConceptApproximationUpper(characteristic_set, concept_block, concept);
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
}

int main() {
    vector<string> attributes;
    set<string> concepts;
    vector<string*> decision_table;
    int num_cases = 0;
    int num_attributes = 0;

    string option;
    bool valid = false;
    while (option != "n" && !valid) {
        cout << "Do you want to start the program? (y/n): ";
        cin >> option;
        if (option == "y") {
            string file;
            cout << "Enter the input file: ";
            cin >> file;
            ifstream inputfile;
            inputfile.open(file);
            if (inputfile.is_open()) {
                parseInput(inputfile, decision_table, attributes, concepts, num_cases, num_attributes);
                // cout << '\n';
                run(decision_table, attributes, concepts, num_cases, num_attributes);
                valid = true;
            } else {
                cout << "Invalid file!" << '\n';
            }
        }
    }
    cout << "Exiting!" << '\n';
    return 0;
}