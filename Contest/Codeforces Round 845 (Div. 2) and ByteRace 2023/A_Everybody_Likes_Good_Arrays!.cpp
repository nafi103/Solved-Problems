#include <bits/stdc++.h>
#define ll long long
using namespace std;
 int main()
{
    int t;
    cin >> t;
    while (t--)
    {
        ll n,cnt = 0;
        cin>>n;
        ll arr[n];
        for (int i = 0; i < n; i++)
        {
            cin >> arr[i];
            if(i>0){
                if(arr[i]%2==arr[i-1]%2)    cnt++;   
            }
        }
        cout<<cnt<<endl;
    }
}