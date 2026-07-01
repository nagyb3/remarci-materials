#include <iostream>
#include <array>
#include <vector>
#include <deque>
#include <forward_list>
#include <list>
#include <set>
#include <map>

struct Add
{
    int x;
    int operator()(int y) const { return x + y; }
};

int main() {
    Add a1;
    a1.x = 1;
    std::cout << a1(2) << std::endl; // 1 + 2

    // vector -> 1 2 3 5 3 4
    // set -> 1 2 3 4 5

    // std::array
    std::array<int, 5> array = {1,2,3,4,5};
    array.size();
    array[0];

    // std::vector
    std::vector<int> vector = {1,2,3,4};
    vector.push_back(5); // 1 2 3 4 5
    vector.pop_back(); // 1 2 3 4
    vector[1];

    // std::deque
    std::deque<int> deque = {1,2,3,4,5};

    // std::forward_list
    std::forward_list<int> forward_list = {1,2,3,4,5};

    // std::list
    std::list<int> list = {1,2,3,4,5};

    // std::set
    std::set<int> mySet;
    mySet.insert(1);
    mySet.insert(1);
    mySet.insert(1);
    mySet.insert(1);

    // std::map
    std::map<int, int> myMap;
    myMap.insert(std::pair<int, int>(7, 10));
    myMap.insert(std::pair<int, int>(7, 11));
    myMap.insert(std::pair<int, int>(7, 12));
    myMap.insert({7, 10}); // modern C++
}