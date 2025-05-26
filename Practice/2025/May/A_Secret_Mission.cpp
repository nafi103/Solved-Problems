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

struct Graph{
    vector<vector<pair<int,int>>>v;
    int n;
    Graph(int N){
        v.resize(N+1);
        n = N;
    }
    void add(int uu, int vv, int wt){
        v[uu].pb({vv,wt});
        v[vv].pb({uu,wt});
    }
    vector<int> dijsktra(int src)
    {
        priority_queue<pair<int,int>, vector<pair<int,int>>, greater<pair<int,int>>> pq;
        vector<int> distance(n, INT_MAX);
        distance[src] = 0;
        pq.push({0, src});
        while (!pq.empty())
        {
            pair<int,int> p = pq.top();
            pq.pop();
            for (auto &[nbr,wt] : v[p.second])
            {
                if (distance[nbr] > max(distance[p.second] , wt))
                {
                    distance[nbr] = max(distance[p.second] , wt);
                    pq.push({distance[nbr], nbr});
                }
            }
        }
        return distance;
    }
};


void solve()
{
    
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
        // google(z);
        solve();
    }
}