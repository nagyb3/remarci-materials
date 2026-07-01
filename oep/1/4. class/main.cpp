#include <iostream>
#include "person.h"

using namespace std;

int main(){
	Person janos;
	//Setterekkel is lehetett volna
	cout << janos << endl;
	janos.birthday();
	cout << janos << endl;
	janos.moveToJanosHegy();
	cout << janos << endl;
}
