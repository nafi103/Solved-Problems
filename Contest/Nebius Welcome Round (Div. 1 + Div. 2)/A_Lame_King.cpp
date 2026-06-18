#include<bits/stdc++.h>
using namespace std;
 void solve(){
    int a,b,ans = 0;
    cin>>a>>b;
    a= abs(a);
    b= abs(b);
    ans = min(a,b)*2;
    int rem = a+b-ans;
    if(rem!=0) ans+= (rem-1)*2+1;
    cout<<ans<<endl;
}   
 int main(){
    int t;
    cin>>t;
    while(t--) solve();
}