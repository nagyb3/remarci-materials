/*
Ajánlott oktatóvideó:
https://www.youtube.com/watch?v=Cq1h1KPoGBU
*/

#include <iostream>
#include <vector>
#include <string>

using namespace std;

void printVector(vector<int> vec);
void printVector(vector<string> vec);

int main(){
	
	vector<int> ints;
	
	ints.push_back(43);
	ints.push_back(467);
	ints.push_back(61);
	ints.push_back(3);
	ints.pop_back(); //utolsó elem kivétele
	
	printVector(ints);
	
	
	vector<string> strings;
	
	strings.push_back("C++");
	strings.push_back("Objektumelvűprogramozás");
	strings.push_back("137-ascsoport");
	strings.push_back("HelloWorld!");
	
	printVector(strings);
	
	return 0;
}

void printVector(vector<int> vec){
	for (unsigned int i = 0; i < vec.size(); ++i){
		cout << vec[i] << " ";
	}
	cout << endl;
}
void printVector(vector<string> vec){
	for (unsigned int i = 0; i < vec.size(); ++i){
		cout << vec[i] << " ";
	}
	cout << endl;
}
