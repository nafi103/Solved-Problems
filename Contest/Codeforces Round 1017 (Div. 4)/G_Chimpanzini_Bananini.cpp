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


void solve()
{
    int mode = 1, sum = 0;
    vector<int>rizz(2,0);
    deque<int>d;
    int q;
    cin>>q;
    while(q--){
        int t;
        cin>>t;
        if(t==3){
            int k;
            cin>>k;
            sum+=k;
            if(mode)
                d.push_back(k);
            else
                d.push_front(k);
            rizz[mode]+=(k*sz(d));
            rizz[mode^1]+=sum;
            cout<<rizz[mode]<<endl;
        }else if(t==2){
            mode^=1;
            cout<<rizz[mode]<<endl;
        }else{
            int el;
            if(mode){
                el=d.back();
                d.pop_back();
                d.push_front(el);
            }else{
                el = d.front();
                d.pop_front();
                d.push_back(el);
            }
            rizz[mode]-=(el*sz(d));
            rizz[mode]+=sum;
            rizz[mode^1]-=sum;
            rizz[mode^1]+=(el*sz(d));
            cout<<rizz[mode]<<endl;
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
        // cout<<"Case "<<z<<": ";
        solve();
    }
}