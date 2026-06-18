#include<bits/stdc++.h>
#define ll long long
using namespace std;
 int main(){
    int t;
    cin>>t;
    while(t--){
        ll n,mxcnt = 1,mncnt = 1;
        cin>>n;
        vector<int>v(n);
        for (int i = 0; i < n; i++)
        {
            cin>>v[i];
        }
        sort(v.begin(),v.end());
        int mn = v[0],mx = v[n-1];
        for (int i = 1; i<n; i++){
            if(v[i]==mn)   mncnt++;
            else break; 
        }
        for (int i = n-2; i>=0; i--){
            if(v[i]==mx)   mxcnt++;
            else break; 
        }
        ll ans = 2*mncnt*mxcnt;
        if(mx==mn)  ans = n*(n-1);
        cout<<ans<<endl;
    }
}