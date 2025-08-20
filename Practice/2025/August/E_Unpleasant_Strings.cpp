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
    string str;
    cin>>str;
    vector<vector<int>>cpos(k);
    for(int i = 0; i<n; i++){
        int numc = str[i]-'a';
        cpos[numc].push_back(i);
    }
    vector<int>dp(n+1,0),window(k,n);
    for(int i = n-1; i>=0; i--){
        dp[i] = inf;
        int numc = str[i]-'a';
        for(int j = 0; j<k; j++){
            dp[i] = min(dp[i],dp[window[j]]);
        }
        dp[i]++;
        window[numc] = min(window[numc],i);
    }
    int q;
    cin>>q;
    while(q--){
        string check;
        cin>>check;
        int pos = -1;
        for(auto &x: check){
            int numc = x-'a';
            auto newpos = upper_bound(all(cpos[numc]),pos);
            if(newpos==cpos[numc].end()){
                pos=n;
                break;
            }
            pos = *newpos;
        }
        cout<<dp[pos]<<endl;
    }
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    for(int z = 1; z<=t; z++){ 
        // cout<<"Case "<<z<<": ";
        solve();
    }
}