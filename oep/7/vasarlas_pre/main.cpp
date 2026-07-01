#include <iostream>
#include "vasarlo.h"
#include "uzlet.h"

using namespace std;

int main()
{
	Vasarlo v("customer1.txt");
	Uzlet u("food.txt", "technical.txt");
	v.vasarol(u);
	return 0;
}