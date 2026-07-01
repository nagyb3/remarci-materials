#include <iostream>
#include "cityenor.h"
#include "countryenor.h"

using namespace std;

//Harmasert: Hány olyan város van, amelyben az osszes nevezetesseg ertekelese 3, vagy annál jobb?
//Otosert:   Add meg azokat az országokat, amelyben van olyan varos, amelynek nincs nevezetessege (esetleg nem létezik, khm khm Győr...)
int main()
{
	cout<<"First task\n";
	try{
		CityEnor e("input.txt");
		int s = 0;
		//TODO
		cout << s << endl;
		
	}catch(CityEnor::FileErrorException err)
	{
		cerr<<"Can't find the input file" <<endl;
	}
	
	cout<<"Second task\n";
	try{
		CountryEnor e2("input.txt");
		//TODO
	}catch(CityEnor::FileErrorException err)
	{
		cerr<<"Can't find the input file" <<endl;
	}
	
	return 0;
}