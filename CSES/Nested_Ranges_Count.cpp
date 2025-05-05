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
template <class T> using pbds = tree<T, null_type, less<T>, rb_tree_tag, tree_order_statistics_node_update >;

#ifndef ONLINE_JUDGE
#include "debug.h"
#define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
#define debug(...)
#endif

/****************************************************************/
using pii = pair<int,int>;

vector<pii>_segment;

void solve()
{
    int n;
    cin>>n;
    vector<pii>bracket;
    _segment.resize(n);
    for(int i = 0; i<n; i++){
        cin>>_segment[i].ff>>_segment[i].ss;
        bracket.pb({_segment[i].ff,i});
        bracket.pb({_segment[i].ss,i});
    }
    vector<int>have(n,0),in(n,0);
    sort(all(bracket),[](const pii &a, const pii &b)->bool{
        if(a.ff==b.ff){
            return _segment[a.ss].ff>_segment[b.ss].ff;
        }
        return a.ff<b.ff;
    });
    unordered_set<int>running;
    pbds<pii>completed,running_val;
    for(auto &[r,idx]: bracket){
        if(running.find(idx)!=running.end()){
            running.erase(running.find(idx));
            running_val.erase({_segment[idx].ff,idx});
            in[idx] = running_val.order_of_key({_segment[idx].ff,INT_MAX});
            int smaller = completed.order_of_key({_segment[idx].ff,INT_MIN});
            have[idx] = sz(completed) - smaller;
            completed.insert({_segment[idx].ff,idx});
        }else{
            running.insert(idx);
            running_val.insert({_segment[idx].ff,idx});
        }
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