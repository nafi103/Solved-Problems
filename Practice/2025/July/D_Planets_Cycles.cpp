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
vector<vector<int>>g,parents;
vector<int>v,len;
vector<bool>visited;
int mx = 20;

void dfs(int node){
    if(visited[node])
        return;
    visited[node] = true;
    if(!visited[v[node]]){
        dfs(v[node]);
        len[node] = len[v[node]] + 1;
    }else{
        len[node] = 1;
    }
    parents[node][0] = v[node];
}

int kthParent(int a, int k){
    if(k<0)
        return -1;
    for(int i = 0; i<mx; i++){
        if(a==-1) return a;
        if(k&(1<<i)){
            a = parents[a][i];
        }
    }
    return a;
}

int query(int x){
    int y = kthParent(x,len[x]), z = kthParent(y,len[y]);
    if(x==y){
        return len[x];
    }else if(z==y){
        if(len[x]>len[y])
            return len[x];
        else{
            if(kthParent(y,len[y]-len[x])==x)
                return len[y];
            else
                return len[x]+len[y];
        }
    }else{
        return len[x]+query(y);
    }
}

void solve()
{
    int n;
    cin>>n;
    g.resize(n);
    parents.assign(n,vector<int>(mx,-1));
    visited.assign(n,false);
    v.resize(n);
    len.assign(n,0);
    for(auto &x: v){
        cin>>x;
        x--;
    }
    for(int i = 0; i<n; i++){
        if(!visited[i])
            dfs(i);
    }
    for(int j = 1; j<mx; j++){
        for(int i = 0; i<n; i++){
            int parent = parents[i][j-1];
            if(parent!=-1)
                parents[i][j] = parents[parent][j-1];
        }
    }
    for(int i = 0; i<n; i++){
        cout<<query(i)<<" ";
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