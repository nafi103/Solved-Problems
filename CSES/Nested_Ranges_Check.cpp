#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
#include<ext/pb_ds/tree_policy.hpp>

using namespace std;
using namespace chrono;
using namespace __gnu_pbds;

/****************************************************************/

#define int long long
#define pi acos(-1.0)
#define mod 998244353
#define inf 1e18+10
#define pb push_back
#define ff first
#define ss second
#define sz(x) (int)(x).size()
#define set_bits(x) __builtin_popcount(x)
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
template <class T> using pbds = tree<T, null_type, less_equal<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
using pii = pair<int,int>;

struct Range{
    pii x;
    int idx;
};

void solve()
{
    int n;
    cin>>n;
    vector<Range>_segment(n);
    for(int i = 0; i<n; i++){
        cin>>_segment[i].x.ff>>_segment[i].x.ss;
        _segment[i].idx = i;
    }
    sort(all(_segment), [](const Range &a, const Range &b)->bool{
        return (a.x.ff==b.x.ff?(a.x.second>b.x.second):(a.x.ff<b.x.ff));
    });
    vector<int>in(n,false),have(n,false);
    int r = INT_MIN;
    priority_queue<pii>pq;
    for(int i = 0; i<n; i++){
        while(!pq.empty() and pq.top().ff>=_segment[i].x.ss){
            have[pq.top().ss] = true;
            pq.pop();
        }
        in[_segment[i].idx] = _segment[i].x.ss<=r;
        r = max(r,_segment[i].x.ss);
        pq.push({_segment[i].x.ss,_segment[i].idx});
    }
    writev(have);
    writev(in);
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