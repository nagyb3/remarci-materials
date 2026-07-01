#include <iostream>

#include "vadasz.h"
#include "vad.h"
#include "trofea.h"

using namespace std;

int main()
{
	Vadasz v("Zsolti", 62, "input.txt");
	//////////////////////////////////////////////////////////////////////////////
	cout << "Hím oroszlánok száma: " << v.hanyHimOroszlan() << endl;
	//////////////////////////////////////////////////////////////////////////////
	double maxSzarv;
	if (v.maxSzarvTomeg(maxSzarv)){
		cout << "Max szarv tomege: " << maxSzarv << endl;
	} else {
		cout << "Nem volt orrszarvu" << endl;
	}
	//////////////////////////////////////////////////////////////////////////////
	if (v.egyezoAgyarhossz()){
		cout << "Volt egyező agyarhosszú elefánt" << endl;
	} else {
		cout << "Nem volt egyező agyarhosszú elefánt" << endl;
	}

	return 0;
}