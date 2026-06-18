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
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define LSOne(x) ((x)&(-x))
#define all(x) x.begin(), x.end()
#define readv(v)      \
    for (auto &x : v) \
    cin >> x
#define writev(v)     \
    for (auto &x : v) \
    cout << x << " "; \
    cout<<endl
#define endl "\n"
#define yes cout<<"YES"<<endl
#define no cout<<"NO"<<endl
#define remove_punctuation(text) regex_replace(text, regex(R"([^\w\s])"), "")
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
    int n,m;
    cin>>n>>m;
    vector<int>a(n),b(m);
    readv(a);
    readv(b);
    vector<vector<int>>dp(n+1,vector<int>(m+1,0));
    vector<vector<pair<int,int>>>par(n+1,vector<pair<int,int>>(m+1,{-1,-1}));
    for(int i = n-1; i>=0; i--){
        for(int j = m-1; j>=0; j--){
            if(a[i]==b[j]){
                dp[i][j] = 1+dp[i+1][j+1];
                par[i][j] = {i+1,j+1};
            }
            else{
                if(dp[i+1][j]>dp[i][j+1]){
                    dp[i][j] = dp[i+1][j];
                    par[i][j] = {i+1,j};
                }else{
                    dp[i][j] = dp[i][j+1];
                    par[i][j] = {i,j+1};
                }
            }
        }
    }
    cout<<dp[0][0]<<endl;
    int r = 0, c = 0;
    while(par[r][c]!=make_pair(-1ll,-1ll)){
        if(a[r]==b[c]){
            cout<<a[r]<<" ";
        }
        tie(r,c) = par[r][c];
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
    // cin >> t;
    for(int z = 1; z<=t; z++){
        // cout<<"Case "<<z<<": ";
        solve();
    }
}