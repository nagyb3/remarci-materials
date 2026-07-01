#include <iostream>
#include <iterator>
#include <vector>
#include <algorithm>
#include <Time>

// forward iterator
/*
template<typename FwdIter, typename Type>
void swap(FwdIter first, FwdIter last, const Type& old_t, const Type& new_t) {
    while (first != last) {
        if (*first == old_t) {
            *first = new_t;
        }
        ++first;
    }
}
*/

template<typename RandIter>
void swap(RandIter first, RandIter last) {
    while ( first < last) {
        std::iter_swap;


        ++first;
    }
}

int main() {
    // input iterator
    /*
    double data[3] = {0};
    std::cout << "adjon meg 3 szamot: ";

    std::istream_iterator<double> pReader(std::cin);
    for (int i = 0; i < 3; ++i) {
        data[i] = >pReader;
        if (i < 2) pReader++;
    }

    for (double elem : data) {
        std::cout << elem << " ";
    }
    */


    // output iterator --> külön kategória
    /*
    std::vector<int> data = {1,2,3,4,5,6,7};
    std::copy(data.begin(), data.end(), std::ostream_iterator<int>(std::cout));
    */


    // forward iterator
    /*
    std::vector<int> data = {1,2,3,4,5,6};
    swap(data.begin(), data.end(), 2, 22);
    swap(data.begin(), data.end(), 5, 55);
    std::copy(data.begin(), data.end(), std::ostream_iterator<int>(std::cout));
    */


   // bidirectional iterator
   /*
   std::vector<int> data = {1,2,3,4,5,6,7};
   std::reverse(data.begin(), data.end());
   */


  // random access iterator
  std::vector<int <data = {1,2,3,4,5,6,7};
  std::srnad(unsgined(time.(nullptr)));
  swap(data.begin(), data.end()); // std::begin(data) std::end(data)
  swap(data.rbegin(), data.rend()); // std::begin(data) std::end(data)
  swap(data.cbegin(), data.cend()); // std::begin(data) std::end(data)
  swap(data.crbegin(), data.crend())); // std::begin(data) std::end(data)
}