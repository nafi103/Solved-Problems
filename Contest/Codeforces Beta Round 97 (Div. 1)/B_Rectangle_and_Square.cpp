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

int sq(int n){
    return n*n;
}

bool is_square(vector<pii>&v){
    int mx = 0, idx = 0;
    for(int i = 1; i<4; i++){
        int d = sq(v[i].ff-v[0].ff) + sq(v[i].ss-v[0].ss);
        if(d>mx){
            mx = d;
            idx = i;
        }
    }
    swap(v[idx],v[2]);
    set<int>s;
    int AB = sq(v[1].ff-v[0].ff) + sq(v[1].ss-v[0].ss);
    int BC = sq(v[1].ff-v[2].ff) + sq(v[1].ss-v[2].ss);
    int CD = sq(v[2].ff-v[3].ff) + sq(v[2].ss-v[3].ss);
    int AD = sq(v[3].ff-v[0].ff) + sq(v[3].ss-v[0].ss);
    int AC = sq(v[0].ff-v[2].ff) + sq(v[0].ss-v[2].ss);
    int BD = sq(v[3].ff-v[1].ff) + sq(v[3].ss-v[1].ss);
    return AB==BC and BC==CD and CD==AD and AC==BD;
}

bool is_rectangle(vector<pii>&v){
    int mx = 0, idx = 0;
    for(int i = 1; i<4; i++){
        int d = sq(v[i].ff-v[0].ff) + sq(v[i].ss-v[0].ss);
        if(d>mx){
            mx = d;
            idx = i;
        }
    }
    swap(v[idx],v[2]);
    set<int>s;
    int AB = sq(v[1].ff-v[0].ff) + sq(v[1].ss-v[0].ss);
    int BC = sq(v[1].ff-v[2].ff) + sq(v[1].ss-v[2].ss);
    int CD = sq(v[2].ff-v[3].ff) + sq(v[2].ss-v[3].ss);
    int AD = sq(v[3].ff-v[0].ff) + sq(v[3].ss-v[0].ss);
    int AC = sq(v[0].ff-v[2].ff) + sq(v[0].ss-v[2].ss);
    int BD = sq(v[3].ff-v[1].ff) + sq(v[3].ss-v[1].ss);
    return AB==CD and BC==AD and AC==BD;
}

void solve()
{   
    int n = 8;
    vector<pii>points(n);
    for(auto &[f,s]: points) cin>>f>>s;
    vector<int>v = {0,0,0,0,1,1,1,1};
    do{
        vector<pii>squ, rect;
        for(int i = 0; i<n; i++){
            if(v[i]) squ.pb(points[i]);
            else rect.pb(points[i]);
        }
        if(is_square(squ) and is_rectangle(rect)){
            cout<<"YES"<<endl;
            for(int i = 0; i<n; i++){
                if(v[i]) cout<<i+1<<" ";
            }
            cout<<endl;
            for(int i = 0; i<n; i++){
                if(!v[i]) cout<<i+1<<" ";
            }
            cout<<endl;
            return;
        }
    }while(next_permutation(v.begin(),v.end()));
    cout<<"NO"<<endl;
}

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int t = 1;
    // cin >> t;
    for(int z = 1; z<=t; z++){
        // google(z);
        solve();
    }
}