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

int32_t main()
{
    // freopen("paint.in", "r", stdin);
    // freopen("paint.out", "w", stdout);
    fastIO;
    cout.precision(10);
    cout.setf(ios::fixed);
    int a,b;
    while(cin>>a>>b and (a or b)){
        vector<int>va,vb;
        int len = max(log10(a)+1, log10(b)+1);
        va.resize(len,0);
        vb.resize(len,0);
        int i = 0;
        while(a){
            va[i++]=a%10;
            a/=10;
        }
        i = 0;
        while(b){
            vb[i++]=b%10;
            b/=10;
        }
        int op = 0, carry = 0;
        for(i = 0; i<len; i++){
            int curr = va[i]+vb[i]+carry;
            carry = 0;
            if(curr>=10){
                carry = 1;
                op++;
            }
        }
        if(op==0){
            cout<<"No carry operation."<<endl;
        }else if(op==1){
            cout<<"1 carry operation."<<endl;
        }else{
            cout<<op<<" carry operations."<<endl;
        }
    }
}