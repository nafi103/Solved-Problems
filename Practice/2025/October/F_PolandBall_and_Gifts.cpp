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
vector<vector<int>>g;
vector<bool>visited;
bitset<1000001> b;

int dfs(int node){
    visited[node] = true;
    int ans = 1;
    for(auto &x: g[node]){
        if(!visited[x])
            ans+=dfs(x);
    }
    return ans;
}

void solve()
{
    int n,k,mx = 0, mn = 0;
    cin>>n>>k;
    vector<int>circle;
    g.resize(n);
    visited.assign(n,false);
    for(int i = 0; i<n; i++){
        int x;
        cin>>x;
        x--;
        g[i].push_back(x);
    }
    for(int i = 0; i<n; i++){
        if(!visited[i] and sz(g[i]))
            circle.push_back(dfs(i));
    }
    b.set(0);
    int cnt[100];
    for(auto &x: circle){
        if(x>=100)
            b|=(b<<x);
        else
            cnt[x]++;
    }
    for(int i = 1; i<100; i++){
        int x = cnt[i];
        if(x==0)
            continue;
        for(int j = 1; j<=x; j<<=1){
            b|=(b<<(j*i));
            x-=j;
        }
        b|=(b<<(x*i));
    }
    if(b[k]){
        mn = k;
    }else{
        mn = k+1;
    }
    int tk = k;
    int extra = 0;
    for(auto &x: circle){
        int have = x/2;
        extra+=(x&1);
        if(have<=tk){
            mx+=have*2;
            tk-=have;
        }else{
            mx+=(tk*2);
            tk = 0;
            break;
        }
    }
    mx+=min(extra,tk);
    cout<<mn<<" "<<mx<<endl;
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