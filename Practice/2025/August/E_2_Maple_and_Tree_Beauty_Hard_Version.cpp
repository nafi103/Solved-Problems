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
int max_level,n, k, l;
vector<int>level_count;

bool check(int len){
    vector<int>tmp;
    tmp.reserve(len);
    for(int i = 0; i<len; i++){
        tmp.push_back(level_count[i]);
    }
    sort(all(tmp),greater<int>());
    int tz = k, to = l;
    for(auto &x: tmp){
        if(tz<to)
            swap(to,tz);
        if(tz>=x)
            tz-=x;
        else
            return false;
    }
    return true;
}

int bs(int l, int r){
    if(l>r)
        return r;
    int mid = (l+r)/2;
    if(check(mid+1))
        return bs(mid+1,r);
    return bs(l,mid-1);
}

void solve()
{
    level_count.clear();
    cin>>n>>k;
    l = n-k;
    vector<int>parent(n+1,-1),level(n+1,0);
    level_count.assign(n+1,0);
    vector<vector<int>>t(n+1);
    for(int i = 2; i<=n; i++){
        int &p = parent[i];
        cin>>p;
        t[p].push_back(i);
        t[i].push_back(p);
    }
    queue<array<int,3>>q;
    q.push({1,-1,0});
    while(!q.empty()){
        auto [node,par,l] = q.front();
        q.pop();
        level[node] = l;
        for(auto &child: t[node]){
            if(child!=par){
                q.push({child,node,l+1});
            }
        }
    }
    max_level = inf;
    level_count[0] = 1;
    for(int i = 2; i<=n; i++){
        level_count[level[i]]++;
        if(sz(t[i])==1)
            max_level = min(max_level,level[i]);
    }
    cout<< 1 + bs(0,max_level)<<endl;
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