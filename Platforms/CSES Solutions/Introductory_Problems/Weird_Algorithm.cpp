#include<bits/stdc++.h>
#define ll long long
using namespace std;


int main(){
    ll n;
    cin>>n;
    while(true){
        cout<<n<<" ";
        if(n==1)    break;
        if(n%2==1)  n = n*3+1;
        else n/=2;
    }
    cout<<endl;
}