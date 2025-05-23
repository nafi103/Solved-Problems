#include<bits/stdc++.h>
#define int long long
using namespace std;
#define all(x) x.begin(), x.end()
const int MAX = 5e6 + 6;

int32_t main() {
    int n;
    cin>>n;
    if(n==2 or n==4){
        cout<<"SAME"<<'\n';
    }else if(n==3){
        cout<<"SQUARE"<<'\n';
    }else{
        cout<<"POWER"<<'\n';
    }
    return 0;
}