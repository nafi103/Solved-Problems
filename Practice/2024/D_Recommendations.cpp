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

void solve()
{
    int n;
    cin>>n;
    using pii = pair<int,int>;
    pii not_present = {-INT_MIN, INT_MAX};
    vector<pii>segments(n),max_segment(n,not_present);
    for(int i = 0; i<n; i++){
        cin>>segments[i].first>>segments[i].second;
    }
    for(int i = 0; i<n; i++){
        for(int j = 0; j<n; j++){
            if(j!=i){
                if(segments[i].first<=segments[j].first and segments[i].second>=segments[j].second){
                    max_segment[j].first = max(max_segment[j].first,segments[i].first );
                    max_segment[j].second = min(max_segment[j].second,segments[i].second );
                }
            }
        }
    }
    for(int i = 0; i<n; i++){
        if(max_segment[i]==not_present){
            cout<<0<<endl;
            continue;
        }else{
            cout<<segments[i].first-max_segment[i].first + max_segment[i].second - segments[i].second<<endl;
        }
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
    cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}