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
    int n,m,k;
    cin>>n>>m>>k;
    vector<vector<int>>pref(n+2*k,vector<int>(m+2*k,0));
    vector<vector<char>>grid(n+2*k,vector<char>(m+2*k,'#'));
    for(int i = k; i<n+2*k; i++){
        for(int j = k; j<m+2*k; j++){
            if(i<n+k and j<m+k)
                cin>>grid[i][j];
            if(grid[i][j]=='g')
                pref[i][j] = 1;
            pref[i][j]+=(pref[i-1][j] + pref[i][j-1] - pref[i-1][j-1]);
        }
    }
    if(k==1){
        cout<<pref[n+2*k-1][m+2*k-1]<<endl;
        return;
    }
    int ck = k-1;
    int waste = inf;
    for(int i = k; i<n+k; i++){
        for(int j = k; j<m+k; j++){
            if(grid[i][j]=='.'){
                int rl = i-ck, cl = j-ck, rr = i+ck, cr = j+ck;
                int psum = pref[rr][cr] - pref[rr][cl-1] - pref[rl-1][cr] + pref[rl-1][cl-1];
                waste = min(waste,psum);
            }
        }
    }
    cout<<pref[n+2*k-1][m+2*k-1]-waste<<endl;
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