#include<bits/stdc++.h>
#define ll long long
using namespace std;
 void solve(){
    ll a,b,c,d;
    cin >> a >> b >> c >> d;
    if(d<b){
        cout<<-1<<endl;
        return;
    }
    ll ans = d-b;
    a+=ans;
    if(a<c){
        cout<<-1<<endl;
        return;
    }
    cout<<ans+(a-c)<<endl;
}
 int main(){
    ll t;
    cin >> t;
    while (t--) solve();
}