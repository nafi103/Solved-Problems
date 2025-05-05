#pragma GCC optimize("O3")
#pragma GCC optimize("Ofast")
#pragma GCC optimize ("unroll-loops")
#include<bits/stdc++.h>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace std;
using namespace __gnu_pbds;
#define ee end()
#define bb begin()
#define ff first
#define ss second
#define int int64_t
#define Int long long
#define vi vector<int>
#define pr pair<int,int>
#define vs vector<string>
#define safe_map unordered_map<long long, long long, custom_hash>
string cdn[]{"NO", "YES"};
const int N = 2e5 + 123;
const int mod = 1e9 + 7;
#define all(x) x.begin(),x.end()
#define fr(i,n) for (int i = 0; i < n; i += 1)
#define make_unique(x) sort(all(x)); x.resize(unique(all(x)) - x.begin())
struct custom_hash {static uint64_t splitmix64(uint64_t x) {x += 0x9e3779b97f4a7c15;x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9;x = (x ^ (x >> 27)) * 0x94d049bb133111eb;return x ^ (x >> 31);}
size_t operator()(uint64_t x) const {static const uint64_t FIXED_RANDOM = chrono::steady_clock::now().time_since_epoch().count();return splitmix64(x + FIXED_RANDOM);}};
typedef tree<int, null_type, less<int>, rb_tree_tag, tree_order_statistics_node_update> ordered_set;
template <typename T> istream& operator>>(istream& in, vector<T>& a) {for(auto &x : a) in >> x; return in;};
template <typename T> ostream& operator<<(ostream& out, vector<T>& a) {for(auto &x : a) out << x << ' '; return out;};
#ifndef ONLINE_JUDGE
#define dbg(...) cerr << "[" << #__VA_ARGS__ << "]:", debug_out(__VA_ARGS__)
#else 
#define dbg(x) 
#endif
void solve(){
    int V, E;
    cin >> V >> E;
    vector<array<int,3>>edges;
    unordered_map<int, vi> adj;
    safe_map dist;
    for(int i=0;i<E;i++) {
        int u, v, c;
        cin >> u >> v >> c;
        edges.push_back({u,v,c});
    }

    /*graph conversion according to difference of subway color */
    for(auto ele : edges){
        int u = ele[0], v = ele[1], c = ele[2];
        adj[c + V].push_back(u);
        adj[c + V].push_back(v);
        adj[u].push_back(c + V);
        adj[v].push_back(c + V);
        dist[c + V] = 1e18;
        dist[u] = 1e18;
        dist[v] = 1e18;
    }
    int src, dest;
    cin >> src >> dest;
    if(src == dest){
        cout << 0 << endl;
        return ;
    }
    dist[src] = 0;
    queue<int> q;
    q.push(src);
    /*shortest path from source to all destnation node*/
    while(!q.empty()){
        int par = q.front();
        if(par == dest){
            cout << dist[dest] / 2 << endl;
            return;
        }
        q.pop();
        for (auto ele : adj[par])
        {
            if(dist[ele] > dist[par] + 1){
                dist[ele] = dist[par] + 1;
                q.push(ele);
            }
        }
    }
    cout << dist[dest]/2 << endl;
}   
int32_t main(){
    int tc = 1;
    cin >> tc;
    for(int i=1;i<=tc;i++){
        //cout << "Case "<<i<<": ";
        solve();
    }
    return 0;
}