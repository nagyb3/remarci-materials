#include <iostream>

#include "vadasz.h"
#include "vad.h"
#include "trofea.h"

using namespace std;

int main()
{
	Vadasz v("Zsolti", 62, "input.txt");

	cout << "Hím oroszlánok száma: " << v.hanyHimOroszlan() << endl;
	return 0;
}