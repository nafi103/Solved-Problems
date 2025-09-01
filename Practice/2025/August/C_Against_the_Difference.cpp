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
#define inf 100
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
vector<int> new_pos,v;
vector<int>dp;

int f(int pos){
    if(pos==-1){
        return 0;
    }
    int &ans = dp[pos];
    if(ans!=-1)
        return ans;
    if(new_pos[pos]==-inf)
        return ans = f(pos-1);
    else{
        return ans = max(f(pos-1),v[pos]+f(new_pos[pos]));
    }
}

void solve()
{
    dp.clear();
    v.clear();
    new_pos.clear();
    int n;
    cin>>n;
    v.resize(n);
    readv(v);
    new_pos.assign(n,-inf);
    dp.assign(n,-1);
    vector<deque<int>>d(n+1);
    for(int i = 0; i<n; i++){
        d[v[i]].push_back(i);
        if(sz(d[v[i]])>v[i])
            d[v[i]].pop_front();
        if(sz(d[v[i]])==v[i]){
            new_pos[i] = d[v[i]][0]-1;
        }
    }
    cout<<f(n-1)<<endl;
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