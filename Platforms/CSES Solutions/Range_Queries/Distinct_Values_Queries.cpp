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
int BLOCK_SIZE;

struct Query {
    int l, r, idx;
    bool operator<(Query other) const
    {
        if (l / BLOCK_SIZE != other.l / BLOCK_SIZE)
            return l / BLOCK_SIZE < other.l / BLOCK_SIZE;
        return ((l / BLOCK_SIZE) & 1) ? (r < other.r) : (r > other.r);
    }
};

void _print(Query &x){
    cerr<<"{"<<x.l<<", "<<x.r<<", "<<x.idx<<"}";
}

int curr_ans = 0;

void add(vector<int>&mp,int x) {
    mp[x]++;
    if (mp[x] == 1) curr_ans++;
}

void remove(vector<int>&mp, int x){
    mp[x]--;
    if(mp[x]==0)
        curr_ans--;
}

void solve()
{
    int n,m;
    cin>>n>>m;
    vector<int>v(n),ans(m);
    map<int,int>cnt;
    for(int i = 0; i<n; i++){
        cin>>v[i];
        if(cnt.count(v[i])==0){
            cnt[v[i]] = sz(cnt);
        }
        v[i] = cnt[v[i]];
    }
    vector<Query>queries(m);
    for(int i = 0; i<m; i++){
        auto &[l,r,id] = queries[i];
        cin>>l>>r;
        l--,r--;
        id = i;
    }
    BLOCK_SIZE = static_cast<int>(sqrt(n));
    sort(all(queries));
    vector<int>track(sz(cnt)+1,0);
    int b = 0, e = -1;
    for(auto &[l,r,id]: queries){
        while (b > l) {
            b--;
            add(track,v[b]);
        }
        while (b < l) {
            remove(track,v[b]);
            b++;
        }
        while (e < r) {
            e++;
            add(track,v[e]);
        }
        while (e > r) {
            remove(track,v[e]);
            e--;
        }
        ans[id] = curr_ans;
    }
    for(auto &x: ans){
        cout<<x<<endl;
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
        // google(z);
        solve();
    }
}