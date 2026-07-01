#pragma once
#include <fstream>
#include <iostream>

struct Statistic {
    int number;
    int count;
};


std::ostream& operator<<(std::ostream& os, const Statistic &s)
{
    os << s.number << " :\t" << s.count << " pieces";
    return os;
}

class Enor
{
    public:
        class FileErrorException : public std::exception { };

        Enor(const std::string &fineName);

        void first() { read(); next(); }
        void next();
        Statistic current() const { return cur; }
        bool end() const { return is_end; }
    private:
        enum Status { abnorm, norm };

        std::ifstream x;
        int cur_num;
        Status st;

        Statistic cur;
        bool is_end;

        void read();
};





void Enor::next()
{
    is_end = (abnorm==st);
    if (!is_end) {
        cur.number = cur_num;
        cur.count = 0;
        while (norm==st && cur_num==cur.number){
            ++cur.count;
            read();
        }
    }
}

void Enor::read()
{
    st = (x >> cur_num) ? norm : abnorm;
}

Enor::Enor(const std::string &fineName)
{
    x.open(fineName);
    if(x.fail()) throw FileErrorException();
}