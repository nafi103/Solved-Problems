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
int n;

void solve()
{
    cin>>n;
    vector<array<int,3>>v(n);
    for(int i = 0; i<n; i++){
        auto &[l,r,id] = v[i];
        cin>>l>>r;
        id = i;
    }
    sort(all(v),[&](array<int,3>&a, array<int,3>&b){
        if(a[0]!=b[0]){
            return a[0]<b[0];
        }
        return a[1]<b[1];
    });
    debug(v)
    vector<int>ans(n,2);
    int ep = v[0][0];
    bool flag = false;
    for(int i = 0; i<n; i++){
        auto &[l,r,id] = v[i];
        if(l>ep){
            flag = true;
            for(int j  = i; j<n; j++){
                auto &[l1,r1,id1] = v[j];
                ans[id1] = 1;
            }
            break;
        }else{
            ep = max(ep,r);
        }
    }
    if(flag){
        writev(ans);
    }else{
        cout<<-1<<endl;
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