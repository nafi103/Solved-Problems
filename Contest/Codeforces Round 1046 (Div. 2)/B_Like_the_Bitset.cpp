#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
const int mod = 998244353;
#define inf 1e18+10
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define endl "\n"
#define fastIO ios::sync_with_stdio(false), cin.tie(nullptr), cout.tie(nullptr)
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/


void solve()
{
    int n,k;
    cin>>n>>k;
    vector<int>s(n);
    for(auto &x: s){
        char c;
        cin>>c;
        x = c-'0';
    }
    if(s[0]==k){
        cout<<"NO"<<endl;
        return;
    }
    for(int i = 1; i<n; i++){
        if(s[i])
            s[i]+=s[i-1];
        if(s[i]==k){
            cout<<"NO"<<endl;
            return;
        }
    }
    cout<<"YES"<<endl;
    vector<int>ans(n,-1);
    int num = n;
    for(int i = 0; i<n; i++){
        if(s[i]==0){
            ans[i] = num--;
        }
    }
    for(int i = 0; i<n; i++){
        if(s[i])
            cout<<(num--)<<" ";
        else
            cout<<ans[i]<<" ";
    }
    cout<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}