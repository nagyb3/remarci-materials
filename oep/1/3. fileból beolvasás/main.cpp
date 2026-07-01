/*
Ajánlott oktatóvideó:
https://www.youtube.com/watch?v=HcONWqVyvlg&index=64&list=PLAE85DE8440AA6B83
és a playlistben a következőek, amik még fájlokkal foglalkoznak
*/

#include <iostream>
#include <fstream>
#include <vector>

using namespace std;

void printIntVec(vector<int> vec);

int main(){
	
	ifstream file;
	file.open("infile.txt");
	
	vector<int> numbers;
	
	int tmp;
	while (file >> tmp){
		numbers.push_back(tmp);
	}
	
	file.close();
	
	printIntVec(numbers);
	
	return 0;
}

void printIntVec(vector<int> vec){
	for (unsigned int i = 0; i < vec.size(); ++i){
		cout << i+1 << ". elem: " << vec[i] << endl;
	}
	cout << endl;
}



