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

int n,r;
bool check(pair<int,int>a){
    int op = 0;
    auto &[f,s] = a;
    while(f and s){
        if(f>=s){
            op+=f/s;
            f%=s;
        }else{
            op+=s/f;
            s%=f;
        }
    }
    if(s==0 and f==1){
        f = 1;
        s = 0;
    }
    return f==0 and s==1 and op==n;
}

int mistake(string &str){
    int cnt = 0;
    for(int i = 1; i<sz(str); i++){
        if(str[i]==str[i-1])
            cnt++;
    }
    return cnt;
}

string make_seq(pair<int,int>a){
    string ans = "";
    auto &[f,s] = a;
    while(f){
        if(f>=s){
            ans+=string(f/s,'B');
            f%=s;
        }else{
            ans+=string(s/f,'T');
            s%=f;
        }
    }
    reverse(all(ans));
    if(ans[0]=='B')
        ans[0] = 'T';
    if(n>1 and ans[n-1]==ans[n-2]){
        ans[n-1] = (ans[n-1]=='T'?'B':'T');
    }
    return ans;
}

void solve()
{
    cin>>n>>r;
    bool flag = true;
    string ans = string(n,'T');
    int ans_mistake = n-1;
    for(int i = 1; i<=r; i++){
        if(check({i,r})){
            flag = false;
            string curr_seq = make_seq({i,r});
            int curr_mistake = mistake(curr_seq); 
            if(curr_mistake<ans_mistake){
                ans = curr_seq;
                ans_mistake = curr_mistake;
            }
        }
        if(check({r,i})){
            flag = false;
            string curr_seq = make_seq({r,i});
            int curr_mistake = mistake(curr_seq); 
            if(curr_mistake<ans_mistake){
                ans = curr_seq;
                ans_mistake = curr_mistake;
            }
        }
    }
    if(flag)
        cout<<"IMPOSSIBLE"<<endl;
    else{
        cout<<ans_mistake<<endl;
        cout<<ans<<endl;
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