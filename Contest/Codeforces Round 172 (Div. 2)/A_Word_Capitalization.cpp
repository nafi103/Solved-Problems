#include <iostream>
#define ll long long
using namespace std;
int main() {
    string str;
    cin>>str;
    if((int)str[0]>=97) str[0]-=32;
    cout<<str<<endl;
}