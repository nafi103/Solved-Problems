#include<bits/stdc++.h>
using namespace std;
 #define int long long
#define endl "\n"
 void solve(){
    int n, ans = LLONG_MAX;
    cin>>n;
    for(int i = 0; i<n; i++){
        int x;
        cin>>x;
        if((x&1)==0){
            ans = min(ans,abs(x));
        }
    }
    cout<<(ans==LLONG_MAX?-1:ans/2)<<endl;
};
 int32_t main(){
    ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr);
    int t = 1;
//    cin>>t;
    for(int z = 1; z<=t; z++){
//        cout<<"Case "<<z<<": ";
        solve();
    }
    return 0;
}