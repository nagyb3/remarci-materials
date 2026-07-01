#include <iostream>
#include "enor.h"

using namespace std;

int main()
{
	try{
		Enor t("input.txt");
		bool l = true;
		t.first();
		while (l && !t.end()){
			l = t.current();
			t.next();
		}
		cout << (l ? "igen" : "nem") << endl;
	}catch(Enor::FileErrorException err)
	{
		cerr<<"Can't find the input file" <<endl;
	}

	return 0;
}