#include <bits/stdc++.h>
#define ll long long
using namespace std;
 void solution()
{
    ll n, q, arrsum = 0, ec = 0, oc = 0, es = 0, os = 0;
    cin >> n >> q;
    ll arr[n];
    for (ll i = 0; i < n; i++)
    {
        cin >> arr[i];
        if (arr[i] % 2 == 0)
            ec++;
        else
            oc++;
        arrsum += arr[i];
    }
    for (int i = 0; i < q; i++)
    {
        ll t, x;
        cin >> t >> x;
        if (t == 0){
            arrsum+=(ec*x);
            if(x%2==1){
                oc+=ec;
                ec=0;
            }
        }else{
            arrsum+=(oc*x);
            if(x%2==1){
                ec+=oc;
                oc=0;
            }
        }
        cout << arrsum<< endl;
    }
}
 int main()
{
    int t;
    cin >> t;
    while (t--)
    {
        solution();
    }
}