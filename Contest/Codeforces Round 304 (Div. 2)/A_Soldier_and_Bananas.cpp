#include <iostream>
#define ll long long
using namespace std;
int main() {
    ll k,n,w, t =0;
    cin>>k>>n>>w;
    for(int i=1;i<=w;i++){
        t+=i*k;
    }
    if(t<=n) cout<<"0";
    else cout<<t-n;
    cout<<"\n";
    return 0;
}